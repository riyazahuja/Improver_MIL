import re
import os


def process_file(file_path):
    # Read the import statements from the file
    with open(file_path, "r") as f:
        import_lines = [line.strip() for line in f.readlines() if line.strip()]

    for import_line in import_lines:
        # Parse the import statement to extract chapter and section information
        match = re.match(
            r"import MIL\.C(\d+)_(\w+)\.solutions\.Solutions_S(\d+)_(\w+)", import_line
        )
        if not match:
            print(f"Skipping invalid import line: {import_line}")
            continue

        chapter_num, chapter_name, section_num, section_name = match.groups()

        # Construct the path to the .lean file
        lean_file_path = f"MIL/C{chapter_num}_{chapter_name}/solutions/Solutions_S{section_num}_{section_name}.lean"

        # Check if the file exists
        if not os.path.exists(lean_file_path):
            print(f"File not found: {lean_file_path}")
            continue

        # Read the content of the .lean file
        with open(lean_file_path, "r") as f:
            content = f.read()

        # Find all instances of "example [name]"
        example_pattern = re.compile(r"^example\s", re.MULTILINE)
        example_matches = example_pattern.finditer(content)

        # Replace instances with "theorem C[xx]_S[yy]_[i]"
        modified_content = content
        offset = 0

        for i, match in enumerate(example_matches):
            start, end = match.span()
            old_text = match.group()
            new_text = f"theorem C{chapter_num}_S{section_num}_{i}"

            # Adjust position based on previous replacements
            adj_start = start + offset
            adj_end = end + offset

            # Replace the text
            modified_content = (
                modified_content[:adj_start] + new_text + modified_content[adj_end:]
            )

            # Update offset for next replacement
            offset += len(new_text) - len(old_text)

        # Write the modified content back to the file
        with open(lean_file_path, "w") as f:
            f.write(modified_content)

        print(f"Processed {len(list(example_matches))} thms from {lean_file_path}")


def main():
    input_file = input("Enter the path to the text file with import statements: ")
    process_file(input_file)
    print("Done processing all files.")


if __name__ == "__main__":
    main()
