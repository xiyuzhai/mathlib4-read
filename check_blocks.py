import re

with open('Mathlib/AlgebraicGeometry/AffineScheme.typ', 'r') as f:
    content = f.read()
    
# Find all code blocks
opening = len(re.findall(r'^```lean$', content, re.MULTILINE))
closing = len(re.findall(r'^```$', content, re.MULTILINE))
print(f'Opening blocks: {opening}')
print(f'Closing blocks: {closing}')
print(f'Difference: {opening - closing}')

# Find line numbers
lines = content.split('\n')
for i, line in enumerate(lines, 1):
    if line.strip() == '```lean':
        print(f'Opening at line {i}')
    elif line.strip() == '```':
        print(f'Closing at line {i}')