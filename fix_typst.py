import re

with open('Mathlib/AlgebraicGeometry/AffineScheme.typ', 'r') as f:
    content = f.read()

# Replace ```lean...``` blocks with #raw blocks
pattern = r'```lean\n(.*?)\n```'
replacement = r'#block(fill: luma(245), inset: 8pt, radius: 4pt)[\n#text(font: "JuliaMono", size: 9pt)[\n\1\n]\n]'

content = re.sub(pattern, replacement, content, flags=re.DOTALL)

with open('Mathlib/AlgebraicGeometry/AffineScheme_fixed.typ', 'w') as f:
    f.write(content)

print("Created fixed version")