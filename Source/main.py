import base64
import sys
from cryptography.hazmat.primitives import hashes
import math
import secrets
import hashlib

class object:
    tag:int
    byteLength:str
    length:int
    data:str
    arrChild = []

    def __init__(self):
        self.tag = 0
        self.byteLength = '00'
        self.length = 0
        self.data = ''

class privKey:
    version:str
    n:str
    e:str
    d:str
    p:str
    q:str
    dp:str
    dq:str
    qinv:str

class pubKey:
    n:str
    e:str

# read pem file with 2 mod private key and public key
def readKey(filename='', mod='priv' or 'pub'):
    file = open(filename, mode="r")
    buffer = ""
    if mod == 'priv':
        for line in file:
            if line != '-----BEGIN PRIVATE KEY-----\n' and line != '-----END PRIVATE KEY-----\n':
                buffer += line.strip('\n')

    elif mod == 'pub':
        for line in file:
            if line != '-----BEGIN PUBLIC KEY-----\n' and line != '-----END PUBLIC KEY-----\n':
                buffer += line.strip('\n')

    return buffer

# handle a hex string 
def __handleTLV(arr:[], buffer:str):
    curByte = 0
    while curByte < len(buffer):
        new_obj = object()
        # read tag
        new_obj.tag = int(buffer[curByte: curByte + 2], 16); curByte += 2
        # read number bytes of real length of value
        new_obj.byteLength = int(buffer[curByte: curByte + 2], 16)

        # if number bytes of real length > 129 byte
        if new_obj.byteLength >= 129:
            curByte += 2
            new_obj.byteLength %= 128
            new_obj.length = int(buffer[curByte: curByte + new_obj.byteLength*2], 16)
            curByte += new_obj.byteLength*2
        # number bytes of real length < 128
        else:
            new_obj.length = int(buffer[curByte: curByte + 2], 16)
            curByte += 2

        # read value
        if new_obj.tag == 3: # first bytes of value is often unused bits
            curByte += 2 
        new_obj.data = buffer[curByte: curByte + new_obj.length*2]; curByte += new_obj.length*2
        arr.append(new_obj)

def __handlePrivKey(buffer:str):
    my_arr:object = []
    temp_arr: object = []
    # TLV level 1
    __handleTLV(my_arr, buffer)
    # TLV level 2
    __handleTLV(temp_arr, my_arr[0].data)
    my_arr.clear()
    # TLV level 3
    __handleTLV(my_arr, temp_arr[2].data)
    temp_arr.clear()
    # TLV level 4
    __handleTLV(temp_arr, my_arr[0].data)

    privKey_arr = temp_arr
    my_privKey = privKey
    my_privKey.version = privKey_arr[0].data
    my_privKey.n = privKey_arr[1].data
    my_privKey.e = privKey_arr[2].data
    my_privKey.d = privKey_arr[3].data
    my_privKey.p = privKey_arr[4].data
    my_privKey.q = privKey_arr[5].data
    my_privKey.dp = privKey_arr[6].data
    my_privKey.dq = privKey_arr[7].data
    my_privKey.qinv = privKey_arr[8].data

    return my_privKey

def __handlePubKey(buffer:str):
    my_arr:object = []
    temp_arr: object = []
    # TLV level 1
    __handleTLV(my_arr, buffer)
    # TLV level 2
    __handleTLV(temp_arr, my_arr[0].data)
    my_arr.clear()
    # TLV level 3
    __handleTLV(my_arr, temp_arr[1].data)
    temp_arr.clear()
    # TLV level 4
    __handleTLV(temp_arr, my_arr[0].data)

    pubKey_arr = temp_arr
    my_pubKey = pubKey
    my_pubKey.n = pubKey_arr[0].data
    my_pubKey.e = pubKey_arr[1].data

    return my_pubKey

def printPrivKey(my_privKey:privKey):
    print(my_privKey.version)
    print(my_privKey.n)
    print(my_privKey.e)
    print(my_privKey.d)
    print(my_privKey.p)
    print(my_privKey.q)
    print(my_privKey.dp)
    print(my_privKey.dq)
    print(my_privKey.qinv)

def printPubKey(my_pubKey:pubKey):
    print(my_pubKey.n)
    print(my_pubKey.e)

# # Support function
def generate_nonzero_random_bytes(length):
    random_bytes = bytearray()
    while len(random_bytes) < length:
        byte = secrets.randbelow(256)
        if byte != 0:
            random_bytes.append(byte)
    return bytes(random_bytes)
# xOR 2 bytes string
def xorBytes(byte_string_1, byte_string_2):
    # Ensure that the two byte strings have the same length
    if len(byte_string_1) != len(byte_string_2):
        raise ValueError("Byte strings must have the same length for XOR operation.")

    # Perform XOR operation byte by byte
    result = bytes([a ^ b for a, b in zip(byte_string_1, byte_string_2)])
    return result
# Mask generation function
def MGF(seed: bytes, length: int, hash_func=hashlib.sha256) -> bytes:
    """Mask generation function."""
    hLen = hash_func().digest_size
    # https://www.ietf.org/rfc/rfc2437.txt
    # 1. If l > 2^32(hLen), output "mask too long" and stop.
    if length > (hLen << 32):
        raise ValueError("mask too long")
    # 2. Let T be the empty octet string.
    T = b""
    # 3. For counter from 0 to \lceil{l / hLen}\rceil-1, do the following:
    # Note: \lceil{l / hLen}\rceil-1 is the number of iterations needed,
    #       but it's easier to check if we have reached the desired length.
    counter = 0
    while len(T) < length:
        # a. Convert counter to an octet string C of length 4 with the primitive I2OSP: C = I2OSP (counter, 4)
        C = int.to_bytes(counter, 4, "big")
        # b. Concatenate the hash of the seed Z and C to the octet string T: T = T || Hash (Z || C)
        T += hash_func(seed + C).digest()
        counter += 1
    # 4. Output the leading l octets of T as the octet string mask.
    return T[:length]

# # RSA Encrypt and Decrypt function
# rsa_padding_mode: pkcs1
def rsa_padding_pkcs1_type2_encrypt(message, my_pubKey:pubKey):
    # Convert modulus and exponent to integers
    n = int(my_pubKey.n, 16)
    e = int(my_pubKey.e, 16)

    # Calculate the length of the key
    key_length = math.ceil(n.bit_length() / 8)

    # Check message length
    if len(message) > key_length - 11:
        raise ValueError('ossl_rsa_padding_add_PKCS1_type_2_ex: data too large for key size')

    # Add PKCS1 type 2 padding
    padding_length = key_length - len(message) - 3
    padding = b'\x00\x02' +  generate_nonzero_random_bytes(padding_length) + b'\x00'

    # Construct the encrypted block
    # EM = '\x00\x02 || Random bytes || x00 || M'
    encoded_message = padding + message

    # Convert the encrypted block to an integer
    encoded_message_int = int.from_bytes(encoded_message, byteorder='big')

    # Encrypt the message
    c = pow(encoded_message_int, e, n)

    encrypted_message = c.to_bytes((c.bit_length() + 7) // 8, 'big')

    return encrypted_message

def rsa_padding_pkcs1_type2_decrypt(ciphertext, privKey):
    # convert ciphertext to int
    ciphertext_int = int.from_bytes(ciphertext, 'big')

    # Decrypt the ciphertext
    encoded_message_int = pow(ciphertext_int, int(privKey.d, 16), int(privKey.n, 16))

    # Convert the decrypted message to a bytes array
    encoded_message = b'\x00' + encoded_message_int.to_bytes((encoded_message_int.bit_length() + 7) // 8, 'big')

    # Check PKCS1 type 2 padding
    if encoded_message[0:2] != b'\x00\x02':
        raise ValueError('Invalid PKCS1 type 2 padding')

    # Find the first non-zero byte after the padding
    padding_start = encoded_message.find(b'\x00', 2)
    if padding_start == -1:
        raise ValueError('Invalid PKCS1 type 2 padding')

    # Retrieve the original message
    message = encoded_message[padding_start + 1:]

    return message

# rsa_padding_mode: oaep, digest: sha256
def rsa_padding_oaep_sha256_encrypt(mess, my_pubKey: pubKey):
    P = b''
    hlen = 32
    n = int(my_pubKey.n, 16)
    e = int(my_pubKey.e, 16)

    lem = math.ceil(n.bit_length() / 8)
    if len(mess) > lem - 2*hlen -1:
        raise IndexError('message too long')
    
    # Generate an octet string PS consisting of emLen-||M||-2hLen-1 zero
    # octets. The length of PS may be 0.
    PS = bytes([0x00] * (lem - len(mess) - 2*hlen - 2))

    # Let pHash = Hash(P)
    digest = hashes.Hash(hashes.SHA256())
    digest.update(P)
    pHash = digest.finalize()

    # DB = pHash || PS || 01 || M
    DB = pHash + PS + b'\x01' + mess
    # Generate a random octet string seed of length hLen.
    seed = generate_nonzero_random_bytes(hlen)
    # Let dbMask = MGF(seed, emLen-hLen).
    dbMask = MGF(seed, lem-hlen-1)
    # Let maskedDB = DB \xor dbMask.
    maskedDB = xorBytes(DB, dbMask)
    # Let seedMask = MGF(maskedDB, hLen).
    seedMask = MGF(maskedDB, hlen)
    # Let maskedSeed = seed \xor seedMask.
    maskedSeed = xorBytes(seed, seedMask)
    # Let EM = maskedSeed || maskedDB
    EM = maskedSeed + maskedDB

    EM_int = int.from_bytes(EM, 'big')
    # encrypt message
    c = pow(EM_int, e, n)
    # convert c to byte and return
    encrypted_message = c.to_bytes((c.bit_length() + 7) // 8, 'big')
    return encrypted_message

def rsa_padding_oaep_sha256_decrypt(ciphertext, my_privKey: privKey):
    hlen = 32
    P = b''
    # convert ciphertext to int
    ciphertext_int = int.from_bytes(ciphertext, 'big')

    # Decrypt the ciphertext
    encoded_message_int = pow(ciphertext_int, int(my_privKey.d, 16), int(my_privKey.n, 16))
    # Convert the decrypted message to a bytes array
    encoded_message = encoded_message_int.to_bytes((encoded_message_int.bit_length() + 7) // 8, 'big')

    lem = len(encoded_message)
    # Let maskedSeed be the first hLen octets of EM and let maskedDB be
    # the remaining ||EM|| - hLen octets.
    maskedSeed = encoded_message[:hlen]
    maskDB = encoded_message[hlen:]
    # Let seedMask = MGF(maskedDB, hLen).
    seedMask = MGF(maskDB, hlen)
    # Let seed = maskedSeed \xor seedMask. 
    seed = xorBytes(maskedSeed, seedMask)
    # Let dbMask = MGF(seed, ||EM|| - hLen).
    dbMask = MGF(seed, lem - hlen)
    # Let DB = maskedDB \xor dbMask.    
    db = xorBytes(maskDB, dbMask)
    # Let pHash = Hash(P), an octet string of length hLen.
    pHashed = db[0:hlen]
    pm = db[hlen:]
    mess_start = pm.find(b'\x01')
    # If there is no 01 octet to separate PS from M, output "decoding
    # error" and stop.
    if mess_start == -1:
        raise ValueError('Decoding error')
    
    digest = hashes.Hash(hashes.SHA256())
    digest.update(P)
    pHash = digest.finalize()
    # If pHashed does not equal pHash, output "decoding error" and stop.
    if pHashed != pHash:
        raise ValueError('Decoding error')

    decrypted_message = pm[mess_start + 1:]

    return decrypted_message

# rsa_padding_mode:none
def rsa_no_padding_encrypt(mess, my_pubKey:pubKey):
    # not the same padding with key
    if(len(mess)) != math.ceil(int(my_pubKey.n, 16).bit_length() / 8):
        raise ValueError('data too small or large for key size')

    mess_int = int.from_bytes(mess, 'big')
    # Calculate cipher
    ciphertext_int = pow(mess_int, int(my_pubKey.e, 16), int(my_pubKey.n, 16))
    # Conver to bytes
    ciphertext = ciphertext_int.to_bytes((ciphertext_int.bit_length() + 7) // 8, 'big')

    return ciphertext

def rsa_no_padding_decrypt(ciphertext, my_privKey: privKey):
     # not the same padding with key
    
    if len(ciphertext) != math.ceil(int(my_privKey.n, 16).bit_length() / 8):
        raise ValueError('cipher too small or large for key size')
    
    ciphertext_int = int.from_bytes(ciphertext, 'big')
    # Calculate mess
    m_int = pow(ciphertext_int, int(my_privKey.d, 16), int(my_privKey.n, 16))
    # Convert to bytes
    m = m_int.to_bytes((m_int.bit_length() + 7) // 8, 'big')
    return m

# # RSA Sign and Verify
# rsa_padding_mode: pkcs1_type1
def rsa_padding_pkcs1_sign(message, my_privKey:privKey, hash_func=hashlib.sha256):
    #  MD2:     (0x)30 20 30 0c 06 08 2a 86 48 86 f7 0d 02 02 05 00 04
    #               10 || H.
    #  MD5:     (0x)30 20 30 0c 06 08 2a 86 48 86 f7 0d 02 05 05 00 04
    #               10 || H.
    #  SHA-1:   (0x)30 21 30 09 06 05 2b 0e 03 02 1a 05 00 04 14 || H.
    #  SHA-256: (0x)30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00
    #               04 20 || H.
    #  SHA-384: (0x)30 41 30 0d 06 09 60 86 48 01 65 03 04 02 02 05 00
    #               04 30 || H.
    #  SHA-512: (0x)30 51 30 0d 06 09 60 86 48 01 65 03 04 02 03 05 00
    #                  04 40 || H.
    digestinfor = b'\x30\x31\x30\x0d\x06\x09\x60\x86\x48\x01\x65\x03\x04\x02\x01\x05\x00\x04\x20'
    ldigestinofor = len(digestinfor)

    # Convert modulus and exponent to integers
    n = int(my_privKey.n, 16)
    d = int(my_privKey.d, 16)

     # Calculate the length of the key
    key_length = math.ceil(n.bit_length() / 8)
    hlen = hash_func().digest_size
    hMess = hash_func(message).digest()

    # Add PKCS1 type 2 padding
    padding_length = key_length - hlen - 3 - ldigestinofor
    padding = b'\x00\x01' + bytes([0xFF] * padding_length) + b'\x00'

    # Construct the encrypted block
    signature = padding + digestinfor + hMess

    # Convert the encrypted block to an integer
    signature_int = int.from_bytes(signature, byteorder='big')

    # Encrypt the signature
    encrypt_sign_int = pow(signature_int, d, n)

    # Return encrypted data as an integer
    encrypt_sign = encrypt_sign_int.to_bytes((encrypt_sign_int.bit_length() + 7) // 8, 'big')

    return encrypt_sign

def rsa_padding_pkcs1_verify(signed, mess, my_pubKey:pubKey, hash_func=hashlib.sha256):
    hlen = hash_func().digest_size
    # Convert signed to int
    signed_int = int.from_bytes(signed, 'big')

    # Decrypt the ciphertext
    decrypt_signature = pow(signed_int, int(my_pubKey.e, 16), int(my_pubKey.n, 16))

    # Convert the decrypted message to a bytes array
    encoded_signature = b'\x00' + decrypt_signature.to_bytes((decrypt_signature.bit_length() + 7) // 8, 'big')

    # Check PKCS1 type 2 padding
    if encoded_signature[0:2] != b'\x00\x01':
        raise ValueError('Invalid PKCS1 type 2 padding')

    # Find the first non-zero byte after the padding
    padding_start = encoded_signature.find(b'\x00', 2)
    if padding_start == -1:
        raise ValueError('Invalid PKCS1 type 2 padding')

    # Retrieve the original signature
    mess_decoded = encoded_signature[-hlen:]

    hMess = hash_func(mess).digest()
    if mess_decoded != hMess:
        return -1, 'Signature Verification Failure' 

    return 1, 'Signature Verified Successfully'

# rsa_padding_mode: pss
def rsa_padding_pss_sign(mess, my_privKey:privKey, hash_func=hashlib.sha256):
    # digest size
    hlen = hash_func().digest_size
    # Convert key to int
    n = int(my_privKey.n, 16)
    d = int(my_privKey.d, 16)
    klen = math.ceil(n.bit_length() / 8)
    dblen = klen - hlen - 1
    # Hash(mess)
    m_hash = hash_func(mess).digest()
    
    salt = generate_nonzero_random_bytes(hlen)
    # DB = PS || \x01 || salt 
    DB = bytes([0x00]*(klen - hlen - hlen - 2)) + b'\x01' + salt
    M = bytes([0x00]*8) +  m_hash + salt
    H = hash_func(M).digest()
    maskH = MGF(H, dblen)
    maskDB = xorBytes(DB, maskH)

    # Set leftmost bit of maskDB to zero
    maskDB = bytes([maskDB[0] & 0x7F]) + maskDB[1:]
    # Concatenate 
    EM = maskDB + H + b'\xbc'
    # Encrypt signature
    EM_int = int.from_bytes(EM, 'big')
    encrypt_EM_int = pow(EM_int, d, n)
    # Covert to bytes and return
    encrypt_EM = encrypt_EM_int.to_bytes((encrypt_EM_int.bit_length() + 7) // 8, 'big')
    return encrypt_EM

def rsa_padding_pss_verify(signature, mess, my_pubKey:pubKey, hash_func=hashlib.sha256):
    # Calculate hash length
    hlen = hash_func().digest_size
    # Covert n, e to int and calculate key length
    n = int(my_pubKey.n, 16)
    e = int(my_pubKey.e, 16)
    klen = math.ceil(n.bit_length() / 8)

    if klen < hlen - hlen + 2:
        return -1, 'Length Error'

    # Decrypt signature
    signature_int = int.from_bytes(signature, 'big')
    decrypt_signature_int = pow(signature_int, e, n)
    # Convert to bytes
    decrypt_signature = decrypt_signature_int.to_bytes((decrypt_signature_int.bit_length() + 7) // 8, 'big')

    if decrypt_signature[-1:] != b'\xbc':
        return -1, 'Rightmost octet is not 0xbc'

    # decrypt_signature = maskDB || H || bc
    H = decrypt_signature[klen-hlen-1:klen-1]
    maskDB = decrypt_signature[:klen - hlen - 1]

    if maskDB[0] & 0x80 != 0:
        return -1, 'Leftmost bit of maskDB not consists of all zero'

    DB = xorBytes(maskDB, MGF(H, klen-hlen - 1, hash_func))
    # DB = 00...00 || \x01 || salt 
    
    if  DB[klen -2*hlen - 2: klen - 2*hlen - 1] != b'\x01':
        return -1, 'Octet at klen - hlen - slen - 2 does not have x01'

    salt_start = DB.find(b'\x01')
    salt = DB[salt_start + 1:]
    # Hash(mess)
    hashed_mess = hash_func(mess).digest()
    # Rehash message and salt and compare
    buffer = bytes([0x00] * 8) + hashed_mess + salt
    padded_hased = hash_func(buffer).digest()

    if H != padded_hased:
        return -1, 'Signature Verification Failure'

    return 1, 'Signature Verified Seccessfully'


def main():
    # decode from base64 to hex string
    priv_buffer = readKey('priv.pem', 'priv')
    priv_buffer = base64.b64decode(priv_buffer).hex()
    my_privKey:privKey = __handlePrivKey(priv_buffer)

    # decode from base64 to hex string
    pub_buffer = readKey('pub.pem', 'pub')
    pub_buffer = base64.b64decode(pub_buffer).hex()
    my_pubKey:pubKey = __handlePubKey(pub_buffer)

    # python main.py -in <plain or mess> -out <cipher or sign> -[encrypt, sign] -pkeyopt rsa_padding_mode: [pss, oaep, none]
    # python main.py -in <cipher or sign> -out <plain or mess> -[decrypt, verify] -pkeyopt rsa_padding_mode: [pss, oaep, none]
    # python main.py -print -[priv or pub]

    # OAEP use for encryption and decryption
    # PSS use for signing and verifying

    # default: 
    #   if rsa_padding_mode:oaep -> rsa_oae_md:sha256, 
    #   rsa_padding_mode:pkcs1
    if len(sys.argv) == 6:
        with open(sys.argv[2], 'rb') as file:
            input = file.read()
        
        if sys.argv[5] == '-encrypt':
            output = rsa_padding_pkcs1_type2_encrypt(input, my_pubKey)
            with open(sys.argv[4], 'wb') as file:
                file.write(output)
            return
        
        elif sys.argv[5] == '-decrypt':
            output = rsa_padding_pkcs1_type2_decrypt(input, my_privKey)
            with open(sys.argv[4], 'wb') as file:
                file.write(output)
            return        
        
        elif sys.argv[5] == '-sign':
            output = rsa_padding_pkcs1_sign(input, my_privKey)
            with open(sys.argv[4], 'wb') as file:
                file.write(output)
            return
        
        elif sys.argv[5] == '-verify':
            with open(sys.argv[4], 'rb') as file:
                mess = file.read()
            
            check, nofi = rsa_padding_pkcs1_verify(input, mess, my_pubKey)
            print(nofi)
            return
    
    elif len(sys.argv) == 9:
        with open(sys.argv[2], 'rb') as file:
            input = file.read()

        if sys.argv[8] == 'pss':
            if sys.argv[5] == '-decrypt' or sys.argv[5] == '-encrypt':
                raise TypeError('PSS used for signing and verifying')
            if sys.argv[5] == '-sign':
                output = rsa_padding_pss_sign(input, my_privKey)
                with open(sys.argv[4], 'wb') as file:
                    file.write(output)
                return
            elif sys.argv[5] == '-verify':
                with open(sys.argv[4], 'rb') as file:
                    mess = file.read()
                check, nofi = rsa_padding_pss_verify(input, mess, my_pubKey)
                print(nofi)
                return
            else:
                raise SyntaxError('Syntax Error')
            
        elif sys.argv[8] == 'oaep':
            with open(sys.argv[2], 'rb') as file:
                input = file.read()

            if sys.argv[5] == '-sign' or sys.argv[5] == '-verify':
                raise TypeError('OAEP do not used for signing and verifying')
            if sys.argv[5] == '-encrypt':
                output = rsa_padding_oaep_sha256_encrypt(input, my_pubKey)
                with open(sys.argv[4], 'wb') as file:
                    file.write(output)
                return
            elif sys.argv[5] == '-decrypt':
                output = rsa_padding_oaep_sha256_decrypt(input, my_privKey)
                with open(sys.argv[4], 'wb') as file:
                    file.write(output)
                return
            else:
                raise SyntaxError('Syntax Error')
            
        elif sys.argv[8] == 'none':
            with open(sys.argv[2], 'rb') as file:
                input = file.read()
            
            if sys.argv[5] == '-sign' or sys.argv[5] == '-verify':
                raise TypeError('Not support')
            if sys.argv[5] == '-encrypt':
                output = rsa_no_padding_encrypt(input, my_pubKey)
                with open(sys.argv[4], 'wb') as file:
                    file.write(output)
                return
            elif sys.argv[5] == '-decrypt':
                output = rsa_no_padding_decrypt(input, my_privKey)
                with open(sys.argv[4], 'wb') as file:
                    file.write(output)
                return
            else:
                raise SyntaxError('Syntax Error')
    elif len(sys.argv) == 3:
        if sys.argv[1] == '-print':
            if sys.argv[2] == 'priv':
                printPrivKey(my_privKey)
                return
            elif sys.argv[2] == 'pub':
                printPubKey(my_pubKey)
                return
            else:
                raise SyntaxError('Syntax Error')
    else:
        raise SyntaxError('Syntax Error')        
    return

if __name__ == '__main__':
    main()

