#!/usr/bin/env python3

with open('Scheme.typ', 'r') as f:
    lines = f.readlines()
    
open_blocks = []
for i, line in enumerate(lines, 1):
    if line.strip().startswith('```'):
        if open_blocks and open_blocks[-1][1] is None:
            # This is a closing block
            open_blocks[-1] = (open_blocks[-1][0], i)
        else:
            # This is an opening block
            open_blocks.append((i, None))

print("Code blocks:")
for start, end in open_blocks:
    if end is None:
        print(f"UNCLOSED block starting at line {start}")
    else:
        print(f"Block from line {start} to {end}")

# Show last few blocks
print("\nLast 3 blocks:")
for start, end in open_blocks[-3:]:
    if end is None:
        print(f"UNCLOSED block starting at line {start}")
        print(f"  Content: {lines[start-1].strip()}")
    else:
        print(f"Block from line {start} to {end}")