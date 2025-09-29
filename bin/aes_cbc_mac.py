import os
import csv
from Crypto.Cipher import AES

# --- Configuration ---
# The name of the output CSV file
output_filename = 'encryption_data.csv'
# The number of random encryption records to generate
number_of_records = 1000
# AES key size in bytes (16 for AES-128, 24 for AES-192, 32 for AES-256)
KEY_SIZE = 16
# AES block size is always 16 bytes
BLOCK_SIZE = 16
# Message size in bytes (must be a multiple of BLOCK_SIZE for this simple example)
MESSAGE_SIZE = 32 

# --- Main Script ---
print(f"Preparing to generate {number_of_records} records into '{output_filename}'...")

# The header row for our CSV file
header = ['key', 'plaintext', 'ciphertext']

try:
    # 'w' means write mode, newline='' prevents extra blank rows
    with open(output_filename, 'w', newline='') as csvfile:
        # Create a writer object to handle CSV writing
        csv_writer = csv.writer(csvfile)
        
        # Write the header row first
        csv_writer.writerow(header)

        # Loop to generate the specified number of records
        for i in range(number_of_records):
            key = os.urandom(KEY_SIZE)
            iv = bytes.fromhex('00000000000000000000000000000000')
            message = os.urandom(MESSAGE_SIZE)

            # key_string = '000102030405060708090a0b0c0d0e0f'
            # key = bytes.fromhex(key_string)
            # message_string = '00112233445566778899aabbccddeeff6A9EE8941F318681A3727155CE20CB9A'
            # #message_string = '6A9EE8941F318681A3727155CE20CB9A00112233445566778899aabbccddeeff'
            # message = bytes.fromhex(message_string[32:] + message_string[:32])
            # iv_string = '00000000000000000000000000000000'
            # iv = bytes.fromhex(iv_string)

            # Create a new AES cipher object in CBC mode
            cipher = AES.new(key, AES.MODE_CBC, iv=iv)
            
            # Encrypt the message
            ciphertext = cipher.encrypt(message)

            # flip the message (convention choice for testbench)
            ciphertext = str(ciphertext.hex())
            ciphertext = ciphertext[32:] + ciphertext[:32]

            message = str(message.hex())
            message = message[32:] + message[:32]

            # Write the data to the CSV file.
            # We convert the bytes to hex strings for easy storage and readability.
            csv_writer.writerow([key.hex(), message, ciphertext])

    print(f"Success! Wrote {number_of_records} records to '{output_filename}'.")

except Exception as e:
    print(f"An error occurred: {e}")