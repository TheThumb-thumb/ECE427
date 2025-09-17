import random

def generate_bitstream(length, ratio_ones):
    """Generate a bitstream of a given length with a specific ratio of 1s."""
    num_ones = int(length * ratio_ones)
    num_zeros = length - num_ones
    bits = [1] * num_ones + [0] * num_zeros
    random.shuffle(bits)
    return bits

def bitstream_to_string(bits):
    """Convert list of bits to string."""
    return ''.join(map(str, bits))

def main():
    bitstream_length = 1024
    step = 0.1

    print("Generating bitstreams with varying 1s/0s ratios:\n")
    
    for i in range(1, 10):
        ratio = round(i * step, 2)
        bitstream = generate_bitstream(bitstream_length, ratio)
        bitstream_str = bitstream_to_string(bitstream)
        num_ones = bitstream.count(1)
        num_zeros = bitstream.count(0)
        print(f"Ratio 1s: {ratio:.1f} -> 1s: {num_ones}, 0s: {num_zeros}")
        print(f"Bitstream Sample (first 64 bits): {bitstream_str[:1024]}\n")

if __name__ == "__main__":
    main()
