#!/usr/bin/env python3
import glob
import re

# Fix literate definitions in all .tex files
for tex_file in glob.glob('*.tex'):
    with open(tex_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Fix the literate definitions that have $...$ incorrectly
    # In literate definitions, we should NOT have dollar signs
    content = re.sub(r'\{\{\$\\([^$]+)\$\}\}', r'{{\\\1}}', content)
    
    # Special cases that need fixing
    content = content.replace('{{$^{-1}$ᵁ}}', '{{$^{-1}U$}}')
    content = content.replace('{{$^{-1}$}}', '{{$^{-1}$}}')
    content = content.replace('{{$^{op}$}}', '{{$^{op}$}}')
    content = content.replace('{{$\\ll$$\\gg$}}', '{{$\\ll\\gg$}}')
    
    with open(tex_file, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"Fixed {tex_file}")

print("Done fixing literate definitions")