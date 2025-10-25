import matplotlib
import matplotlib.pyplot as plt
import numpy as np

def plot_hex_distribution(filepath="rrand_output.txt", output_image="hex_distribution.png"):
    """
    Reads a file containing line-separated 64-bit hexadecimal values (8 bytes per line),
    extracts all 8 bytes from each line, and plots their distribution as a histogram.

    Args:
        filepath (str): Path to the input text file.
        output_image (str): Path to save the output image file.
    """
    values = []
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    # Parse as 64-bit integer
                    word = int(line, 16)
                    # Extract 8 bytes (LSB first)
                    for i in range(8):
                        byte = (word >> (8 * i)) & 0xFF
                        values.append(byte)
                except ValueError:
                    print(f"Warning: Skipping invalid line in {filepath}: {line}")

        if not values:
            print("Error: No valid data found in the file.")
            return

        # --- Plotting the Distribution ---
        plt.style.use('tableau-colorblind10')
        fig, ax = plt.subplots(figsize=(12, 7))

        bins = np.arange(-0.5, 256.5, 1)
        ax.hist(values, bins=bins, color='skyblue', edgecolor='black')

        ax.set_title('Distribution of Random Bytes (from 64-bit words)', fontsize=16, fontweight='bold')
        ax.set_xlabel('Byte Value (0–255)', fontsize=12)
        ax.set_ylabel('Frequency', fontsize=12)
        ax.set_xlim([-0.5, 255.5])
        
        # Ideal frequency line
        ideal_frequency = len(values) / 256
        ax.axhline(y=ideal_frequency, color='r', linestyle='--', linewidth=1.5,
                   label=f'Ideal Mean Frequency ({ideal_frequency:.2f})')
        ax.legend()

        plt.tight_layout()

        # --- Save plot to file ---
        plt.savefig(output_image, dpi=300)
        print(f"Plot saved as '{output_image}'")

        # --- Show if GUI backend available ---
        try:
            backend = matplotlib.get_backend().lower()
            if not any(k in backend for k in ['agg', 'pdf', 'svg', 'ps']):
                plt.show()
            else:
                print(f"No GUI backend detected (using '{backend}'), skipping plt.show().")
        except Exception:
            print("Unable to display the plot window — saved instead.")

    except FileNotFoundError:
        print(f"Error: The file '{filepath}' was not found.")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    plot_hex_distribution()




# import matplotlib
# import matplotlib.pyplot as plt
# import numpy as np

# def plot_hex_distribution(filepath="rrand_output.txt", output_image="hex_distribution.png"):
#     """
#     Reads a file containing line-separated 8-bit hexadecimal values,
#     parses them, and plots their distribution as a histogram.

#     Args:
#         filepath (str): Path to the input text file.
#         output_image (str): Path to save the output image file.
#     """
#     values = []
#     try:
#         with open(filepath, 'r') as f:
#             for line in f:
#                 try:
#                     value = int(line.strip(), 16)
#                     values.append(value)
#                 except ValueError:
#                     print(f"Warning: Skipping invalid line in {filepath}: {line.strip()}")
        
#         if not values:
#             print("Error: No valid data found in the file.")
#             return

#         # --- Plotting the Distribution ---
#         plt.style.use('tableau-colorblind10')
#         fig, ax = plt.subplots(figsize=(12, 7))

#         bins = np.arange(-0.5, 256.5, 1)
#         ax.hist(values, bins=bins, color='skyblue', edgecolor='black')

#         ax.set_title('Distribution of 8-bit Random Values', fontsize=16, fontweight='bold')
#         ax.set_xlabel('Value (0–255)', fontsize=12)
#         ax.set_ylabel('Frequency', fontsize=12)
#         ax.set_xlim([-0.5, 255.5])
        
#         # Ideal frequency line
#         ideal_frequency = len(values) / 256
#         ax.axhline(y=ideal_frequency, color='r', linestyle='--', linewidth=1.5,
#                    label=f'Ideal Mean Frequency ({ideal_frequency:.2f})')
#         ax.legend()

#         plt.tight_layout()

#         # --- Save plot to file ---
#         plt.savefig(output_image, dpi=300)
#         print(f"Plot saved as '{output_image}'")

#         # --- Try to show if a GUI backend is available ---
#         try:
#             backend = matplotlib.get_backend().lower()
#             if not any(k in backend for k in ['agg', 'pdf', 'svg', 'ps']):
#                 plt.show()
#             else:
#                 print(f"No GUI backend detected (using '{backend}'), skipping plt.show().")
#         except Exception:
#             print("Unable to display the plot window — saved instead.")

#     except FileNotFoundError:
#         print(f"Error: The file '{filepath}' was not found.")
#     except Exception as e:
#         print(f"An unexpected error occurred: {e}")

# if __name__ == "__main__":
#     plot_hex_distribution()
# import matplotlib.pyplot as plt
# import numpy as np

# def plot_hex_distribution(filepath="rrand_output.txt"):
#     """
#     Reads a file containing line-separated 8-bit hexadecimal values,
#     parses them, and plots their distribution as a histogram.

#     Args:
#         filepath (str): The path to the input text file.
#     """
#     values = []
#     try:
#         with open(filepath, 'r') as f:
#             for line in f:
#                 # Strip whitespace and convert hex string to integer
#                 try:
#                     # The base 16 tells int() to interpret the string as hexadecimal
#                     value = int(line.strip(), 16)
#                     values.append(value)
#                 except ValueError:
#                     print(f"Warning: Skipping invalid line in {filepath}: {line.strip()}")
        
#         if not values:
#             print("Error: No valid data found in the file.")
#             return

#         # --- Plotting the Distribution ---
#         plt.style.use('tableau-colorblind10')
#         fig, ax = plt.subplots(figsize=(12, 7))

#         # Create a histogram with 256 bins, one for each possible 8-bit value
#         # The range is set from -0.5 to 255.5 to center the bars on integer values
#         bins = np.arange(-0.5, 256.5, 1)
#         ax.hist(values, bins=bins, color='skyblue', edgecolor='black')

#         # --- Formatting the Plot ---
#         ax.set_title('Distribution of 8-bit Random Values', fontsize=16, fontweight='bold')
#         ax.set_xlabel('Value (0-255)', fontsize=12)
#         ax.set_ylabel('Frequency', fontsize=12)
#         ax.set_xlim([-0.5, 255.5]) # Set x-axis limits to match the data range
        
#         # Add a horizontal line for the ideal average frequency for a uniform distribution
#         ideal_frequency = len(values) / 256
#         ax.axhline(y=ideal_frequency, color='r', linestyle='--', linewidth=1.5, label=f'Ideal Mean Frequency ({ideal_frequency:.2f})')
#         ax.legend()

#         plt.tight_layout()
#         plt.show()

#     except FileNotFoundError:
#         print(f"Error: The file '{filepath}' was not found.")
#     except Exception as e:
#         print(f"An unexpected error occurred: {e}")

# if __name__ == "__main__":
#     # The script assumes 'rrand_output.txt' is in the same directory.
#     # If not, provide the full path to the file.
#     plot_hex_distribution()

# count_bits.py
# Counts number of 1s and 0s in a text file of 8-bit hex values (one per line)

# def count_bits_from_file(filename="rrand_output.txt"):
#     ones = 0
#     zeros = 0

#     with open(filename, 'r') as f:
#         for line in f:
#             line = line.strip()
#             if not line:
#                 continue  # skip empty lines

#             try:
#                 # Parse the hex value (e.g. "af" or "0xAF")
#                 value = int(line, 16)
#                 print(f"hex value: {line}")
#             except ValueError:
#                 print(f"Skipping invalid line: {line}")
#                 continue

#             # Convert to 8-bit binary string
#             bits = f"{value:08b}"
#             print(f"binary value: {bits}")

#             # Count bits
#             ones += bits.count('1')
#             zeros += bits.count('0')

#     return ones, zeros


# if __name__ == "__main__":
#     filename = "rrand_output.txt"  # change if needed
#     ones, zeros = count_bits_from_file(filename)

#     print(f"File: {filename}")
#     print(f"Total 1s: {ones}")
#     print(f"Total 0s: {zeros}")
#     total = ones + zeros
#     if total > 0:
#         print(f"Ratio of 1s: {ones / total:.4f}")
#         print(f"Ratio of 0s: {zeros / total:.4f}")
