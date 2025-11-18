# import random

# def generate_bitstring(num_bits=1024, percent_ones=50):
#     """
#     Generate a random binary string of a given length with a given percentage of 1s.

#     Args:
#         num_bits (int): Total number of bits in the string.
#         percent_ones (float): Percentage of bits that should be 1s (0-100).

#     Returns:
#         str: A 1024-bit string with the specified ratio of 1s to 0s.
#     """
#     if not (0 <= percent_ones <= 100):
#         raise ValueError("percent_ones must be between 0 and 100")

#     num_ones = int(num_bits * percent_ones / 100)
#     num_zeros = num_bits - num_ones

#     bits = ['1'] * num_ones + ['0'] * num_zeros
#     random.shuffle(bits)

#     return ''.join(bits)


# if __name__ == "__main__":
#     percent = float(input("Enter percentage of 1s (0-100): "))
#     bitstring = generate_bitstring(1024, percent)
#     print(f"\nGenerated 1024-bit string with {percent}% 1s:\n")
#     print(bitstring)

import random

def generate_bitstring(num_bits=1024, percent_ones=50):
    """Generate a bitstring with a given percentage of 1s."""
    num_ones = int(num_bits * percent_ones / 100)
    num_zeros = num_bits - num_ones
    bits = ['1'] * num_ones + ['0'] * num_zeros
    random.shuffle(bits)
    return ''.join(bits)

def generate_systemverilog_vectors(num_vectors=101, num_bits=1024, var_name="test_vec"):
    """
    Generate SystemVerilog initialization statements for bit vectors.

    Args:
        num_vectors (int): Number of vectors (0% to 100% inclusive → 101 total)
        num_bits (int): Bit width of each vector
        var_name (str): Name of the array (e.g., test_vec)
    """
    sv_lines = []
    for i in range(num_vectors):
        bitstring = generate_bitstring(num_bits, i)  # i% 1s
        line = f"assign {var_name}[{i}] = {num_bits}'b{bitstring};"
        sv_lines.append(line)
    return '\n'.join(sv_lines)

if __name__ == "__main__":
    sv_code = generate_systemverilog_vectors(num_vectors=101, num_bits=1024, var_name="test_vec")
    
    with open("generated_test_vecs.sv", "w") as f:
        f.write("logic [1023:0] test_vec [0:100];\n\n")
        f.write(sv_code)
    
    print("✅ Generated 'generated_test_vecs.sv' with 0%–100% 1s bitstrings (1024 bits each).")
