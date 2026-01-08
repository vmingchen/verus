verus! {

pub open spec fn is_continuation_byte(byte: u8) -> bool {
    (byte & 0x80) != 0
}

pub open spec fn max_varint_bytes() -> usize {
    10
}

pub open spec fn min_padding() -> usize {
    15
}

// Test multiline ensures with block expression
pub exec fn decode_varint_u64_padded(data: &[u8]) -> (result: Result<(u64, usize), &'static str>)
    requires
        data.len() >= min_padding(),
    ensures
        result.is_ok() ==> {
            let (value, consumed) = result.unwrap();
            consumed <= max_varint_bytes() &&
            consumed >= 1 &&
            !is_continuation_byte(data[consumed - 1]) &&
            consumed <= data.len()
        },
        result.is_err() ==> {
            true
        },
{
    Ok((0, 1))
}

// Test nested block expressions in ensures
pub exec fn complex_ensures(x: u32, y: u32) -> (result: (u32, u32))
    ensures
        result.0 == x ==> {
            result.1 == y
        },
        result.1 > 0 ==> {
            let sum = result.0 + result.1;
            sum > 0
        },
{
    (x, y)
}

}
