#!/usr/bin/env python3
"""
Simple converter from LaTeX to Typst - preserves most content as-is
"""

import sys
from pathlib import Path

def convert_file(input_path):
    """Convert a .tex file to .typ file"""
    
    input_path = Path(input_path)
    output_path = input_path.with_suffix('.typ')
    
    with open(input_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    output = []
    
    # Add Typst header
    output.append('#set text(font: "New Computer Modern", size: 11pt)')
    output.append('#set page(margin: 1in)')
    output.append('#set heading(numbering: "1.")')
    output.append('')
    
    in_document = False
    in_lstlisting = False
    
    for line in lines:
        # Start of document
        if r'\begin{document}' in line:
            in_document = True
            continue
        if not in_document:
            continue
        if r'\end{document}' in line:
            break
            
        # Skip maketitle
        if r'\maketitle' in line:
            continue
            
        # Handle title specially
        if r'\title{' in line and '{' in line and '}' in line:
            start = line.find('{') + 1
            end = line.rfind('}')
            title = line[start:end]
            # Clean up title
            title = title.replace(r'\\', ' ').replace(r'\large ', '').replace(r'\texttt{', '').replace('}', '')
            output.append('#align(center)[')
            output.append(f'  #text(size: 18pt, weight: "bold")[{title}]')
            output.append(']')
            output.append('')
            continue
            
        # Skip author and date
        if r'\author{' in line or r'\date{' in line:
            continue
            
        # Convert sections - extract content between braces
        if r'\section{' in line and '{' in line and '}' in line:
            start = line.find('{') + 1
            end = line.rfind('}')
            section = line[start:end]
            output.append(f'= {section}')
            output.append('')
            continue
        if r'\subsection{' in line and '{' in line and '}' in line:
            start = line.find('{') + 1
            end = line.rfind('}')
            subsection = line[start:end]
            output.append(f'== {subsection}')
            output.append('')
            continue
            
        # Handle code blocks
        if r'\begin{lstlisting}' in line:
            in_lstlisting = True
            output.append('```lean')
            continue
        if r'\end{lstlisting}' in line:
            in_lstlisting = False
            output.append('```')
            output.append('')
            continue
        if in_lstlisting:
            output.append(line.rstrip())
            continue
            
        # Handle environments - just skip the begin/end lines
        if r'\begin{' in line or r'\end{' in line:
            continue
            
        # For other lines, preserve mostly as-is but clean obvious LaTeX
        if line.strip():
            # Basic replacements
            line = line.replace(r'\textbf{', '*').replace('}', '*', 1)
            line = line.replace(r'\texttt{', '`')
            line = line.replace(r'\emph{', '_')
            line = line.replace(r'\\', ' ')
            line = line.replace(r'\noindent', '')
            
            # Don't output empty lines
            if line.strip():
                output.append(line.strip())
        elif output and output[-1] != '':
            # Add blank line for paragraph separation
            output.append('')
    
    # Write output
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(output))
    
    print(f"Converted {input_path} to {output_path}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        # Convert all .tex files
        import glob
        tex_files = glob.glob("Mathlib/**/*.tex", recursive=True)
        for tex_file in tex_files:
            try:
                convert_file(tex_file)
            except Exception as e:
                print(f"Error converting {tex_file}: {e}")
    else:
        convert_file(sys.argv[1])