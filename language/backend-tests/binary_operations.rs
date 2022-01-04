pub fn test_usize_operations (i : usize) {
    let o = 8 / (i & 7);
    let o = 8 + (i | 7);
    let o = 8 - (i + 7);
    let o = 8 * (i - 7);
    let o = 8 & (i * 7);
    
    let o = 8 < 4;
    let o = 8 <= 4;
    let o = 8 > 4;
    let o = 8 >= 4;
    
    let o = 8 != 4;
    let o = 8 == 4;
}

