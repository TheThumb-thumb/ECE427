import matplotlib.pyplot as plt
import numpy as np

def plot_hex_distribution(filepath="../vcs/rrand_output.txt"):
    """
    Reads a file containing line-separated 8-bit hexadecimal values,
    parses them, and plots their distribution as a histogram.

    Args:
        filepath (str): The path to the input text file.
    """
    values = []
    try:
        with open(filepath, 'r') as f:
            for line in f:
                # Strip whitespace and convert hex string to integer
                try:
                    # The base 16 tells int() to interpret the string as hexadecimal
                    value = int(line.strip(), 16)
                    values.append(value)
                except ValueError:
                    print(f"Warning: Skipping invalid line in {filepath}: {line.strip()}")
        
        if not values:
            print("Error: No valid data found in the file.")
            return

        # --- Plotting the Distribution ---
        plt.style.use('seaborn-v0_8-whitegrid')
        fig, ax = plt.subplots(figsize=(12, 7))

        # Create a histogram with 256 bins, one for each possible 8-bit value
        # The range is set from -0.5 to 255.5 to center the bars on integer values
        bins = np.arange(-0.5, 256.5, 1)
        ax.hist(values, bins=bins, color='skyblue', edgecolor='black')

        # --- Formatting the Plot ---
        ax.set_title('Distribution of 8-bit Random Values', fontsize=16, fontweight='bold')
        ax.set_xlabel('Value (0-255)', fontsize=12)
        ax.set_ylabel('Frequency', fontsize=12)
        ax.set_xlim([-0.5, 255.5]) # Set x-axis limits to match the data range
        
        # Add a horizontal line for the ideal average frequency for a uniform distribution
        ideal_frequency = len(values) / 256
        ax.axhline(y=ideal_frequency, color='r', linestyle='--', linewidth=1.5, label=f'Ideal Mean Frequency ({ideal_frequency:.2f})')
        ax.legend()

        plt.tight_layout()
        plt.show()

    except FileNotFoundError:
        print(f"Error: The file '{filepath}' was not found.")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    # The script assumes 'rrand_output.txt' is in the same directory.
    # If not, provide the full path to the file.
    plot_hex_distribution()