#!/usr/bin/env python3
"""
Fix Typst file formatting to use raw blocks with proper syntax highlighting
"""

import re

with open('Mathlib/AlgebraicGeometry/AffineScheme.typ', 'r') as f:
    content = f.read()

# Replace the #block...#text pattern with raw blocks that preserve formatting
pattern = r'#block\(fill: luma\(245\), inset: 8pt, radius: 4pt\)\[\s*#text\(font: "JuliaMono", size: 9pt\)\[\s*(.*?)\s*\]\s*\]'

def replace_block(match):
    code = match.group(1)
    # Use raw block with lang parameter for syntax highlighting
    return f'```lean\n{code}\n```'

content = re.sub(pattern, replace_block, content, flags=re.DOTALL)

# Write to a new file first to test
with open('Mathlib/AlgebraicGeometry/AffineScheme_better.typ', 'w') as f:
    f.write(content)

print("Created improved version with raw blocks")