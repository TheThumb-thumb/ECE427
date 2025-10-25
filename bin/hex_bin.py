#!/usr/bin/env python3
"""
hex_to_bin.py — Convert a text file of hexadecimal values to binary.

Each line in the input file should contain one hexadecimal value.
The output file will contain one binary value per line.
"""

def hex_to_bin(input_file="rrand_output.txt", output_file="data_triv"):
    """
    Converts hexadecimal values in a text file to binary and writes the result.

    Args:
        input_file (str): Path to the input text file (hex values per line).
        output_file (str): Path to the output text file (binary values per line).
    """
    try:
        with open(input_file, 'r') as infile, open(output_file, 'w') as outfile:
            line_count = 0
            for line in infile:
                hex_str = line.strip()
                if not hex_str:
                    continue
                try:
                    # Convert from hex to binary (preserve full width)
                    value = int(hex_str, 16)
                    bit_length = len(hex_str) * 4  # 1 hex digit = 4 bits
                    bin_str = format(value, f'0{bit_length}b')
                    outfile.write(bin_str + '\n')
                    line_count += 1
                except ValueError:
                    print(f"Warning: Skipping invalid hex line: {hex_str}")

        print(f"✅ Successfully converted {line_count} lines to binary.")
        print(f"Output written to: {output_file}")

    except FileNotFoundError:
        print(f"❌ Error: The file '{input_file}' was not found.")
    except Exception as e:
        print(f"⚠️ Unexpected error: {e}")


if __name__ == "__main__":
    hex_to_bin()
