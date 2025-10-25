import random

def generate_string(total_length=1024):
    result = []
    current_bit = random.choice(['0', '1'])
    
    while len(result) < total_length:
        run_length = random.choice([21, 31])
        # make sure we don't exceed total_length
        run_length = min(run_length, total_length - len(result))
        result.extend([current_bit] * run_length)
        # flip bit for next run
        current_bit = '1' if current_bit == '0' else '0'
    
    return "".join(result)

s = generate_string()
print(s)
print("Length:", len(s))
