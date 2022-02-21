// Import hacspec and all needed definitions.
use hacspec_lib::*;

array!(OpTableType, 12, usize);

macro_rules! sha_spec {
    ($type:ident, $name:ident,
     $to_be_block:ident,
     $block_size:ident, $len_size:ident, $k_size:ident,
     $block:ident, $digest:ident, $round_constants_table:ident, $hash_typ:ident, $op_table:ident, $ktable:ident,  $hash_init:ident,
     $ch:ident, $maj:ident, $sigma:ident, $schedule:ident, $shuffle:ident, $compress:ident, $hash:ident,) => {
        fn $ch(x: $type, y: $type, z: $type) -> $type {
            (x & y) ^ ((!x) & z)
        }

        fn $maj(x: $type, y: $type, z: $type) -> $type {
            (x & y) ^ ((x & z) ^ (y & z))
        }

        fn $sigma(x: $type, i: usize, op: usize) -> $type {
            let mut tmp: $type = x.rotate_right($op_table[3 * i + 2]);
            if op == 0 {
                tmp = x >> $op_table[3 * i + 2]
            }
            x.rotate_right($op_table[3 * i]) ^ x.rotate_right($op_table[3 * i + 1]) ^ tmp
        }

        fn $schedule(block: $block) -> $round_constants_table {
            let b: Seq<$type> = block.$to_be_block();
            let mut s = $round_constants_table::new();
            for i in 0..$k_size {
                if i < 16 {
                    s[i] = b[i];
                } else {
                    let t16 = s[i - 16];
                    let t15 = s[i - 15];
                    let t7 = s[i - 7];
                    let t2 = s[i - 2];
                    let s1 = $sigma(t2, 3, 0);
                    let s0 = $sigma(t15, 2, 0);
                    s[i] = s1 + t7 + s0 + t16;
                }
            }
            s
        }

        fn $shuffle(ws: $round_constants_table, hashi: $hash_typ) -> $hash_typ {
            let mut h = hashi;
            for i in 0..$k_size {
                let a0 = h[0];
                let b0 = h[1];
                let c0 = h[2];
                let d0 = h[3];
                let e0 = h[4];
                let f0 = h[5];
                let g0 = h[6];
                let h0: $type = h[7];

                let t1 = h0 + $sigma(e0, 1, 1) + $ch(e0, f0, g0) + $ktable[i] + ws[i];
                let t2 = $sigma(a0, 0, 1) + $maj(a0, b0, c0);

                h[0] = t1 + t2;
                h[1] = a0;
                h[2] = b0;
                h[3] = c0;
                h[4] = d0 + t1;
                h[5] = e0;
                h[6] = f0;
                h[7] = g0;
            }
            h
        }

        fn $compress(block: $block, h_in: $hash_typ) -> $hash_typ {
            let s = $schedule(block);
            let mut h = $shuffle(s, h_in);
            for i in 0..8 {
                h[i] = h[i] + h_in[i];
            }
            h
        }

        pub fn $hash(msg: &ByteSeq) -> $digest {
            let mut h = $hash_init;
            // FIXME: #96 use exact_chunks
            let mut last_block = $block::new();
            let mut last_block_len = 0;
            for i in 0..msg.num_chunks($block_size) {
                let (block_len, block) = msg.get_chunk($block_size, i);
                if block_len < $block_size {
                    last_block = $block::new().update_start(&block);
                    last_block_len = block_len;
                } else {
                    let compress_input = $block::from_seq(&block);
                    h = $compress(compress_input, h);
                }
            }

            last_block[last_block_len] = U8(0x80u8);
            let len_bist = U64((msg.len() * 8) as u64);
            if last_block_len < $block_size - $len_size {
                last_block = last_block.update($block_size - $len_size, &U64_to_be_bytes(len_bist));
                h = $compress(last_block, h);
            } else {
                let mut pad_block = $block::new();
                pad_block = pad_block.update($block_size - $len_size, &U64_to_be_bytes(len_bist));
                h = $compress(last_block, h);
                h = $compress(pad_block, h);
            }

            $digest::from_seq(&h.to_be_bytes())
        }

        pub fn $name(msg: &ByteSeq) -> $digest {
            $hash(msg)
        }
    };
}

const BLOCK_SIZE_256: usize = 64;
const LEN_SIZE_256: usize = 8;
pub const K_SIZE_256: usize = 64;
pub const HASH_SIZE_256: usize = 256 / 8;

bytes!(Block_256, BLOCK_SIZE_256);

bytes!(Sha256Digest, HASH_SIZE_256);

array!(RoundConstantsTable_256, K_SIZE_256, U32);

array!(Hash_256, 8, U32);

const OP_TABLE_256: OpTableType = OpTableType([2, 13, 22, 6, 11, 25, 7, 18, 3, 17, 19, 10]);

#[rustfmt::skip]
const K_TABLE_256: RoundConstantsTable_256 = RoundConstantsTable_256(secret_array!(
    U32,
    [
        0x428a_2f98u32, 0x7137_4491u32, 0xb5c0_fbcfu32, 0xe9b5_dba5u32, 0x3956_c25bu32,
        0x59f1_11f1u32, 0x923f_82a4u32, 0xab1c_5ed5u32, 0xd807_aa98u32, 0x1283_5b01u32,
        0x2431_85beu32, 0x550c_7dc3u32, 0x72be_5d74u32, 0x80de_b1feu32, 0x9bdc_06a7u32,
        0xc19b_f174u32, 0xe49b_69c1u32, 0xefbe_4786u32, 0x0fc1_9dc6u32, 0x240c_a1ccu32,
        0x2de9_2c6fu32, 0x4a74_84aau32, 0x5cb0_a9dcu32, 0x76f9_88dau32, 0x983e_5152u32,
        0xa831_c66du32, 0xb003_27c8u32, 0xbf59_7fc7u32, 0xc6e0_0bf3u32, 0xd5a7_9147u32,
        0x06ca_6351u32, 0x1429_2967u32, 0x27b7_0a85u32, 0x2e1b_2138u32, 0x4d2c_6dfcu32,
        0x5338_0d13u32, 0x650a_7354u32, 0x766a_0abbu32, 0x81c2_c92eu32, 0x9272_2c85u32,
        0xa2bf_e8a1u32, 0xa81a_664bu32, 0xc24b_8b70u32, 0xc76c_51a3u32, 0xd192_e819u32,
        0xd699_0624u32, 0xf40e_3585u32, 0x106a_a070u32, 0x19a4_c116u32, 0x1e37_6c08u32,
        0x2748_774cu32, 0x34b0_bcb5u32, 0x391c_0cb3u32, 0x4ed8_aa4au32, 0x5b9c_ca4fu32,
        0x682e_6ff3u32, 0x748f_82eeu32, 0x78a5_636fu32, 0x84c8_7814u32, 0x8cc7_0208u32,
        0x90be_fffau32, 0xa450_6cebu32, 0xbef9_a3f7u32, 0xc671_78f2u32
    ]
));

const HASH_INIT_256: Hash_256 = Hash_256(secret_array!(
    U32,
    [
        0x6a09e667u32,
        0xbb67ae85u32,
        0x3c6ef372u32,
        0xa54ff53au32,
        0x510e527fu32,
        0x9b05688cu32,
        0x1f83d9abu32,
        0x5be0cd19u32
    ]
));

sha_spec!(
    U32,
    sha256,
    to_be_U32s,
    
    BLOCK_SIZE_256,
    LEN_SIZE_256,
    K_SIZE_256,

    Block_256,
    Sha256Digest,
    RoundConstantsTable_256,
    Hash_256,
    OP_TABLE_256,
    K_TABLE_256,
    HASH_INIT_256,
    
    ch_256,
    maj_256,
    sigma_256,
    schedule_256,
    shuffle_256,
    compress_256,
    hash_256,
);

const BLOCK_SIZE_512: usize = 128;
const LEN_SIZE_512: usize = 16;
pub const K_SIZE_512: usize = 80;
pub const HASH_SIZE_512: usize = 512 / 8;

bytes!(Block_512, BLOCK_SIZE_512);

bytes!(Sha512Digest, HASH_SIZE_512);

array!(RoundConstantsTable_512, K_SIZE_512, U64);

array!(Hash_512, 8, U64);

const OP_TABLE_512: OpTableType = OpTableType([28, 34, 39, 14, 18, 41, 1, 8, 7, 19, 61, 6]);

#[rustfmt::skip]
const K_TABLE_512: RoundConstantsTable_512 = RoundConstantsTable_512(secret_array!(
    U64,
    [
        0x428a2f98d728ae22u64, 0x7137449123ef65cdu64, 0xb5c0fbcfec4d3b2fu64, 0xe9b5dba58189dbbcu64, 
        0x3956c25bf348b538u64, 0x59f111f1b605d019u64, 0x923f82a4af194f9bu64, 0xab1c5ed5da6d8118u64, 
        0xd807aa98a3030242u64, 0x12835b0145706fbeu64, 0x243185be4ee4b28cu64, 0x550c7dc3d5ffb4e2u64, 
        0x72be5d74f27b896fu64, 0x80deb1fe3b1696b1u64, 0x9bdc06a725c71235u64, 0xc19bf174cf692694u64, 
        0xe49b69c19ef14ad2u64, 0xefbe4786384f25e3u64, 0x0fc19dc68b8cd5b5u64, 0x240ca1cc77ac9c65u64, 
        0x2de92c6f592b0275u64, 0x4a7484aa6ea6e483u64, 0x5cb0a9dcbd41fbd4u64, 0x76f988da831153b5u64, 
        0x983e5152ee66dfabu64, 0xa831c66d2db43210u64, 0xb00327c898fb213fu64, 0xbf597fc7beef0ee4u64, 
        0xc6e00bf33da88fc2u64, 0xd5a79147930aa725u64, 0x06ca6351e003826fu64, 0x142929670a0e6e70u64, 
        0x27b70a8546d22ffcu64, 0x2e1b21385c26c926u64, 0x4d2c6dfc5ac42aedu64, 0x53380d139d95b3dfu64, 
        0x650a73548baf63deu64, 0x766a0abb3c77b2a8u64, 0x81c2c92e47edaee6u64, 0x92722c851482353bu64, 
        0xa2bfe8a14cf10364u64, 0xa81a664bbc423001u64, 0xc24b8b70d0f89791u64, 0xc76c51a30654be30u64, 
        0xd192e819d6ef5218u64, 0xd69906245565a910u64, 0xf40e35855771202au64, 0x106aa07032bbd1b8u64, 
        0x19a4c116b8d2d0c8u64, 0x1e376c085141ab53u64, 0x2748774cdf8eeb99u64, 0x34b0bcb5e19b48a8u64, 
        0x391c0cb3c5c95a63u64, 0x4ed8aa4ae3418acbu64, 0x5b9cca4f7763e373u64, 0x682e6ff3d6b2b8a3u64, 
        0x748f82ee5defb2fcu64, 0x78a5636f43172f60u64, 0x84c87814a1f0ab72u64, 0x8cc702081a6439ecu64, 
        0x90befffa23631e28u64, 0xa4506cebde82bde9u64, 0xbef9a3f7b2c67915u64, 0xc67178f2e372532bu64, 
        0xca273eceea26619cu64, 0xd186b8c721c0c207u64, 0xeada7dd6cde0eb1eu64, 0xf57d4f7fee6ed178u64, 
        0x06f067aa72176fbau64, 0x0a637dc5a2c898a6u64, 0x113f9804bef90daeu64, 0x1b710b35131c471bu64, 
        0x28db77f523047d84u64, 0x32caab7b40c72493u64, 0x3c9ebe0a15c9bebcu64, 0x431d67c49c100d4cu64, 
        0x4cc5d4becb3e42b6u64, 0x597f299cfc657e2au64, 0x5fcb6fab3ad6faecu64, 0x6c44198c4a475817u64
    ]
));

const HASH_INIT_512: Hash_512 = Hash_512(secret_array!(
    U64,
    [
        0x6a09e667f3bcc908u64,
        0xbb67ae8584caa73bu64,
        0x3c6ef372fe94f82bu64,
        0xa54ff53a5f1d36f1u64,
        0x510e527fade682d1u64,
        0x9b05688c2b3e6c1fu64,
        0x1f83d9abfb41bd6bu64,
        0x5be0cd19137e2179u64
    ]
));


sha_spec!(
    U64,
    sha512,
    to_be_U64s,
    
    BLOCK_SIZE_512,
    LEN_SIZE_512,
    K_SIZE_512,

    Block_512,
    Sha512Digest,
    RoundConstantsTable_512,
    Hash_512,
    OP_TABLE_512,
    K_TABLE_512,
    HASH_INIT_512,
    
    ch_512,
    maj_512,
    sigma_512,
    schedule_512,
    shuffle_512,
    compress_512,
    hash_512,
);
