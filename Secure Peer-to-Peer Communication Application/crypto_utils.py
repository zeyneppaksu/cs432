from Crypto.PublicKey import RSA
from Crypto.Signature import pkcs1_15
from Crypto.Hash import SHA256
from Crypto.PublicKey import ECC
from Crypto.Hash import HMAC, SHA256, SHAKE128
from Crypto.Random import get_random_bytes


def load_rsa_key(filepath):
    with open(filepath, "rb") as f:
        return RSA.import_key(f.read())
    
def verify_signature(message: bytes, signature: bytes, public_key) -> bool:
    try:

        h = SHA256.new(message)
        pkcs1_15.new(public_key).verify(h, signature)
        return True
    
    except (ValueError, TypeError):
        return False


def load_rsa_public_key(filepath):
    with open(filepath, 'rb') as f:
        key_data = f.read()
        return RSA.import_key(key_data)
    
def generate_ecdh_keypair():
    """
    Returns (private_key_obj, public_key_obj) on curve P-256.
    DO NOT export to bytes here – let the caller decide.
    """
    priv = ECC.generate(curve='P-256')
    return priv, priv.public_key()

def derive_session_key(peer_pub_key: ECC.EccKey,
                       priv_key:      ECC.EccKey) -> bytes:
    """
    Standard ECDH:  KS = X-coord( d_A * Q_B ),  32-byte big-endian.
    Both keys **must** be ECC objects on the same curve.
    """
    if peer_pub_key.curve != priv_key.curve:
        raise ValueError("Curve mismatch in ECDH")
    shared_point = priv_key.d * peer_pub_key.pointQ        # EC scalar-mult
    return int(shared_point.x).to_bytes(32, "big")         # 256-bit KS

# ────────────────────────────────────────────────
#  Symmetric helpers
# ────────────────────────────────────────────────
def hmac_sha256(key: bytes, data: bytes) -> bytes:
    return HMAC.new(key, data, digestmod=SHA256).digest()

def shake128_expand(seed: bytes, length: int) -> bytes:
    """XOF – single call, returns `length` bytes."""
    xof = SHAKE128.new(); xof.update(seed)
    return xof.read(length)

def update_iv(old_iv: bytes) -> bytes:
    """Derive next IV in the IV chain (16 bytes)"""
    xof = SHAKE128.new(); xof.update(old_iv)
    return xof.read(16)