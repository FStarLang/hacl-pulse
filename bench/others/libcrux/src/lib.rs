// C ABI for libcrux-ml-dsa, used by bench/others/ops_libcrux.h.
// Keygen from a 32-byte seed, deterministic signing (rnd = 0), empty context.
// Keys/signatures are copied in and out of libcrux's owned types (a few KB
// memcpy, negligible next to the operations themselves).
use core::slice;
use libcrux_ml_dsa::{ml_dsa_44, ml_dsa_65, ml_dsa_87};

macro_rules! ffi {
    ($m:ident, $sk:ty, $vk:ty, $sig:ty, $kp:ident, $sg:ident, $vf:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $kp(pk: *mut u8, sk: *mut u8, xi: *const u8) {
            let kp = $m::generate_key_pair(*(xi as *const [u8; 32]));
            let v = kp.verification_key.as_slice();
            let s = kp.signing_key.as_slice();
            slice::from_raw_parts_mut(pk, v.len()).copy_from_slice(v);
            slice::from_raw_parts_mut(sk, s.len()).copy_from_slice(s);
        }

        #[no_mangle]
        pub unsafe extern "C" fn $sg(sig: *mut u8, sk: *const u8, m: *const u8, n: usize) -> i32 {
            let sk = <$sk>::new(*(sk as *const [u8; <$sk>::len()]));
            match $m::sign(&sk, slice::from_raw_parts(m, n), b"", [0u8; 32]) {
                Ok(s) => {
                    let s = s.as_slice();
                    slice::from_raw_parts_mut(sig, s.len()).copy_from_slice(s);
                    0
                }
                Err(_) => -1,
            }
        }

        #[no_mangle]
        pub unsafe extern "C" fn $vf(pk: *const u8, m: *const u8, n: usize, sig: *const u8) -> i32 {
            let vk = <$vk>::new(*(pk as *const [u8; <$vk>::len()]));
            let sg = <$sig>::new(*(sig as *const [u8; <$sig>::len()]));
            match $m::verify(&vk, slice::from_raw_parts(m, n), b"", &sg) {
                Ok(()) => 0,
                Err(_) => -1,
            }
        }
    };
}

ffi!(ml_dsa_44, ml_dsa_44::MLDSA44SigningKey, ml_dsa_44::MLDSA44VerificationKey,
     ml_dsa_44::MLDSA44Signature, libcrux_mldsa44_keypair, libcrux_mldsa44_sign, libcrux_mldsa44_verify);
ffi!(ml_dsa_65, ml_dsa_65::MLDSA65SigningKey, ml_dsa_65::MLDSA65VerificationKey,
     ml_dsa_65::MLDSA65Signature, libcrux_mldsa65_keypair, libcrux_mldsa65_sign, libcrux_mldsa65_verify);
ffi!(ml_dsa_87, ml_dsa_87::MLDSA87SigningKey, ml_dsa_87::MLDSA87VerificationKey,
     ml_dsa_87::MLDSA87Signature, libcrux_mldsa87_keypair, libcrux_mldsa87_sign, libcrux_mldsa87_verify);
