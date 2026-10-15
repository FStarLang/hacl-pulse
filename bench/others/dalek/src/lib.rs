use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use x25519_dalek::{PublicKey, StaticSecret};

#[no_mangle]
pub unsafe extern "C" fn dalek_x25519(out: *mut u8, sk: *const u8, pk: *const u8) {
    let s = StaticSecret::from(*(sk as *const [u8; 32]));
    let p = PublicKey::from(*(pk as *const [u8; 32]));
    *(out as *mut [u8; 32]) = s.diffie_hellman(&p).to_bytes();
}

/// Expands a 32-byte seed into an opaque SigningKey (returned boxed).
#[no_mangle]
pub unsafe extern "C" fn dalek_ed25519_key(seed: *const u8) -> *mut SigningKey {
    Box::into_raw(Box::new(SigningKey::from_bytes(&*(seed as *const [u8; 32]))))
}

#[no_mangle]
pub unsafe extern "C" fn dalek_ed25519_public(k: *const SigningKey, pk: *mut u8) {
    *(pk as *mut [u8; 32]) = (*k).verifying_key().to_bytes();
}

#[no_mangle]
pub unsafe extern "C" fn dalek_ed25519_sign(k: *const SigningKey, sig: *mut u8, m: *const u8, n: usize) {
    let s = (*k).sign(std::slice::from_raw_parts(m, n));
    *(sig as *mut [u8; 64]) = s.to_bytes();
}

#[no_mangle]
pub unsafe extern "C" fn dalek_ed25519_verify(pk: *const u8, m: *const u8, n: usize, sig: *const u8) -> i32 {
    let Ok(vk) = VerifyingKey::from_bytes(&*(pk as *const [u8; 32])) else { return 0 };
    let s = Signature::from_bytes(&*(sig as *const [u8; 64]));
    vk.verify(std::slice::from_raw_parts(m, n), &s).is_ok() as i32
}
