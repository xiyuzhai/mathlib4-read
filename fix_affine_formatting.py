#!/usr/bin/env python3
"""
Fix AffineScheme.typ to use proper raw blocks with syntax highlighting
"""

import re

with open('Mathlib/AlgebraicGeometry/AffineScheme.typ', 'r') as f:
    lines = f.readlines()

output = []
i = 0

# Add the leancode function definition at the beginning
preamble_added = False

while i < len(lines):
    line = lines[i]
    
    # Add leancode function after the header settings
    if not preamble_added and line.startswith('#set heading'):
        output.append(line)
        output.append('\n')
        output.append('// Define a custom code block for Lean code with syntax highlighting\n')
        output.append('#let leancode(code) = {\n')
        output.append('  block(\n')
        output.append('    fill: luma(245),\n')
        output.append('    inset: 8pt,\n')
        output.append('    radius: 4pt,\n')
        output.append('    width: 100%,\n')
        output.append('    raw(code, lang: "lean", block: true)\n')
        output.append('  )\n')
        output.append('}\n')
        preamble_added = True
        i += 1
        continue
    
    # Check for the start of a #block pattern
    if line.strip().startswith('#block(fill: luma(245)'):
        # Collect the entire block
        block_lines = []
        j = i
        bracket_count = 1
        
        # Skip the first line
        j += 1
        
        # Find the matching closing bracket
        while j < len(lines) and bracket_count > 0:
            if '#text(font: "JuliaMono"' in lines[j]:
                # Skip the text line
                j += 1
                # Collect the actual code until we hit the closing brackets
                code_lines = []
                while j < len(lines):
                    if lines[j].strip() == ']':
                        # End of code
                        break
                    code_lines.append(lines[j].rstrip())
                    j += 1
                
                # Skip the closing brackets
                while j < len(lines) and lines[j].strip() in [']', ']']:
                    j += 1
                
                # Create the leancode block
                code = '\n'.join(code_lines)
                output.append(f'#leancode("{code}")\n')
                i = j
                break
            j += 1
        
        if i == j:
            # Couldn't parse, keep original
            output.append(line)
            i += 1
    else:
        output.append(line)
        i += 1

# Write the fixed version
with open('Mathlib/AlgebraicGeometry/AffineScheme_fixed.typ', 'w') as f:
    f.writelines(output)

print("Created AffineScheme_fixed.typ with improved formatting")