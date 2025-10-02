import json
from Crypto.Cipher import AES

key_string = '000102030405060708090a0b0c0d0e0f'
key = bytes.fromhex(key_string)
#message_string = '00112233445566778899aabbccddeeff6A9EE8941F318681A3727155CE20CB9A'
message_string = '6A9EE8941F318681A3727155CE20CB9A00112233445566778899aabbccddeeff'
message = bytes.fromhex(message_string)
iv_string = '00000000000000000000000000000000'
iv = bytes.fromhex(iv_string)

print(f"Key length: {len(key)} bytes")
print(f"Message length: {len(message)} bytes")
print(f"IV length: {len(iv)} bytes")


cipher = AES.new(key, AES.MODE_CBC, iv=iv)
ciphertext = cipher.encrypt(message) 
ciphertext = str(ciphertext.hex())
ciphertext = ciphertext[32:] + ciphertext[:32]

print("Ciphertext (in hex):", ciphertext)

print("Ciphertext length (in bytes):", len(ciphertext))
