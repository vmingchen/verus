use verus_syn::visit_mut::{self, VisitMut};
use verus_syn::*;

/// Visitor that strips Verus specifications and proof code
pub struct StripVisitor {
    /// Track nested ghost/proof context depth (used in future phases)
    #[allow(dead_code)]
    ghost_depth: u32,

    /// Are we currently inside an exec function?
    inside_exec_fn: bool,

    /// Accumulated non-fatal errors/warnings
    warnings: Vec<String>,
}

impl StripVisitor {
    pub fn new() -> Self {
        Self {
            ghost_depth: 0,
            inside_exec_fn: false,
            warnings: Vec::new(),
        }
    }

    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }
}

impl Default for StripVisitor {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper function to check if a function is spec or proof mode
fn is_spec_or_proof_fn(mode: &FnMode) -> bool {
    matches!(
        mode,
        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_)
    )
}

/// Helper function to check if a type is Ghost<T> or Tracked<T>
fn is_ghost_or_tracked_type(ty: &Type) -> bool {
    match ty {
        Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                let ident = segment.ident.to_string();
                ident == "Ghost" || ident == "Tracked"
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Helper function to check if a function argument is ghost or tracked
fn is_ghost_or_tracked_arg(arg: &FnArg) -> bool {
    // Check tracked token
    if arg.tracked.is_some() {
        return true;
    }

    // Check if type is Ghost<T> or Tracked<T>
    match &arg.kind {
        FnArgKind::Typed(pat_type) => is_ghost_or_tracked_type(&pat_type.ty),
        FnArgKind::Receiver(_) => false,
    }
}

/// Helper function to check if a field is ghost or tracked
fn is_ghost_or_tracked_field(field: &Field) -> bool {
    matches!(field.mode, DataMode::Ghost(_) | DataMode::Tracked(_))
}

/// Helper function to check if an expression is a proof expression
/// that should be removed
fn is_proof_expr(expr: &Expr) -> bool {
    match expr {
        // Proof blocks and quantifiers: proof { ... }, forall|x| ..., exists|x| ..., choose|x| ...
        Expr::Unary(ExprUnary { op, .. }) => matches!(
            op,
            UnOp::Proof(_) | UnOp::Forall(_) | UnOp::Exists(_) | UnOp::Choose(_)
        ),

        // Ghost operators
        Expr::View(_) => true,   // @ operator
        Expr::BigAnd(_) => true, // &&& operator
        Expr::BigOr(_) => true,  // ||| operator

        // Binary operators with ghost-only operations
        Expr::Binary(bin) => matches!(
            bin.op,
            BinOp::Imply(_) | BinOp::Exply(_) | BinOp::Equiv(_) // ==>, <==, <==>
        ),

        // Verus-specific assertion expressions
        Expr::Assert(_) => true,
        Expr::Assume(_) => true,
        Expr::AssertForall(_) => true,

        // Assertion macros (will be refined in later phases)
        Expr::Macro(m) => {
            let name = m.mac.path.segments.last().map(|s| s.ident.to_string());
            matches!(
                name.as_deref(),
                Some("assert") | Some("assume") | Some("proof") | Some("calc")
            )
        }

        _ => false,
    }
}

impl VisitMut for StripVisitor {
    fn visit_file_mut(&mut self, file: &mut File) {
        // Visit all items first
        for item in &mut file.items {
            self.visit_item_mut(item);
        }

        // Filter out spec/proof items
        file.items.retain(|item| match item {
            Item::Fn(f) => !is_spec_or_proof_fn(&f.sig.mode),
            // Keep all other items for now
            _ => true,
        });
    }

    fn visit_item_mut(&mut self, item: &mut Item) {
        match item {
            Item::Fn(f) => {
                // Skip spec/proof functions - they'll be filtered by parent
                if is_spec_or_proof_fn(&f.sig.mode) {
                    return;
                }
                self.visit_item_fn_mut(f);
            }
            _ => {
                // Delegate to default visitor for other items
                visit_mut::visit_item_mut(self, item);
            }
        }
    }

    fn visit_item_fn_mut(&mut self, func: &mut ItemFn) {
        // Strip specifications from signature
        // Use the built-in method!
        func.sig.spec.erase_spec_fields();
        func.sig.mode = FnMode::Default;

        // Strip ghost/tracked parameters
        // Need to work with Punctuated - collect, filter, and recreate
        let filtered: Vec<_> = func
            .sig
            .inputs
            .iter()
            .filter(|arg| !is_ghost_or_tracked_arg(arg))
            .cloned()
            .collect();
        func.sig.inputs = filtered.into_iter().collect();

        // Visit function body
        self.inside_exec_fn = true;
        self.visit_block_mut(&mut func.block);
        self.inside_exec_fn = false;
    }

    fn visit_impl_item_fn_mut(&mut self, func: &mut ImplItemFn) {
        // Skip spec/proof impl methods
        if is_spec_or_proof_fn(&func.sig.mode) {
            return;
        }

        // Strip specifications from signature
        func.sig.spec.erase_spec_fields();
        func.sig.mode = FnMode::Default;

        // Strip ghost/tracked parameters
        let filtered: Vec<_> = func
            .sig
            .inputs
            .iter()
            .filter(|arg| !is_ghost_or_tracked_arg(arg))
            .cloned()
            .collect();
        func.sig.inputs = filtered.into_iter().collect();

        // Visit function body
        self.inside_exec_fn = true;
        self.visit_block_mut(&mut func.block);
        self.inside_exec_fn = false;
    }

    fn visit_trait_item_fn_mut(&mut self, func: &mut TraitItemFn) {
        // Skip spec/proof trait methods
        if is_spec_or_proof_fn(&func.sig.mode) {
            return;
        }

        // Strip specifications from signature
        func.sig.spec.erase_spec_fields();
        func.sig.mode = FnMode::Default;

        // Strip ghost/tracked parameters
        let filtered: Vec<_> = func
            .sig
            .inputs
            .iter()
            .filter(|arg| !is_ghost_or_tracked_arg(arg))
            .cloned()
            .collect();
        func.sig.inputs = filtered.into_iter().collect();

        // Visit function body if present
        if let Some(ref mut block) = func.default {
            self.inside_exec_fn = true;
            self.visit_block_mut(block);
            self.inside_exec_fn = false;
        }
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        // First visit all child statements
        for stmt in &mut block.stmts {
            self.visit_stmt_mut(stmt);
        }

        // Then filter out ghost/proof statements
        block.stmts.retain(|stmt| match stmt {
            Stmt::Local(l) => {
                // Remove ghost/tracked variables
                l.ghost.is_none() && l.tracked.is_none()
            }
            Stmt::Expr(e, _) => {
                // Remove proof expressions
                !is_proof_expr(e)
            }
            Stmt::Macro(m) => {
                // Remove proof/spec macros
                !is_proof_macro(&m.mac)
            }
            _ => true,
        });
    }

    fn visit_item_struct_mut(&mut self, item_struct: &mut ItemStruct) {
        // Visit fields and filter ghost/tracked
        match &mut item_struct.fields {
            Fields::Named(fields) => {
                let filtered: Vec<_> = fields
                    .named
                    .iter()
                    .filter(|field| !is_ghost_or_tracked_field(field))
                    .cloned()
                    .collect();
                fields.named = filtered.into_iter().collect();
            }
            Fields::Unnamed(fields) => {
                let filtered: Vec<_> = fields
                    .unnamed
                    .iter()
                    .filter(|field| !is_ghost_or_tracked_field(field))
                    .cloned()
                    .collect();
                fields.unnamed = filtered.into_iter().collect();
            }
            Fields::Unit => {}
        }

        // Continue with default visitor for other parts
        visit_mut::visit_item_struct_mut(self, item_struct);
    }

    fn visit_item_enum_mut(&mut self, item_enum: &mut ItemEnum) {
        // Visit each variant and strip ghost/tracked fields
        for variant in &mut item_enum.variants {
            match &mut variant.fields {
                Fields::Named(fields) => {
                    let filtered: Vec<_> = fields
                        .named
                        .iter()
                        .filter(|field| !is_ghost_or_tracked_field(field))
                        .cloned()
                        .collect();
                    fields.named = filtered.into_iter().collect();
                }
                Fields::Unnamed(fields) => {
                    let filtered: Vec<_> = fields
                        .unnamed
                        .iter()
                        .filter(|field| !is_ghost_or_tracked_field(field))
                        .cloned()
                        .collect();
                    fields.unnamed = filtered.into_iter().collect();
                }
                Fields::Unit => {}
            }
        }

        // Continue with default visitor for other parts
        visit_mut::visit_item_enum_mut(self, item_enum);
    }

    // TODO Phase 3: Add expression visitors for more complex stripping
    // fn visit_expr_mut(&mut self, expr: &mut Expr) { ... }
}

/// Helper function to check if a macro is a proof/spec macro that should be removed
fn is_proof_macro(mac: &Macro) -> bool {
    let name = mac.path.segments.last().map(|s| s.ident.to_string());
    matches!(
        name.as_deref(),
        Some("proof")
            | Some("calc")
            | Some("assert_forall_by")
            | Some("assert_by")
            | Some("open_invariant")
            | Some("open_local_invariant")
    )
}
