from Crypto.PublicKey import RSA
from Crypto.Signature import pkcs1_15
from Crypto.Hash import SHA256

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
