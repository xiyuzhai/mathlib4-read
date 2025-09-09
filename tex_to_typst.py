#!/usr/bin/env python3
"""
Convert LaTeX files to Typst format
"""

import re
import sys
from pathlib import Path

def convert_tex_to_typst(content):
    """Convert LaTeX content to Typst format"""
    
    lines = content.split('\n')
    output = []
    in_lstlisting = False
    in_document = False
    skip_preamble = True
    
    for line in lines:
        # Skip preamble until \begin{document}
        if r'\begin{document}' in line:
            skip_preamble = False
            in_document = True
            continue
        if skip_preamble:
            continue
            
        # Skip \end{document}
        if r'\end{document}' in line:
            break
            
        # Handle title, author, date
        if r'\maketitle' in line:
            continue
        if line.startswith(r'\title{'):
            title = re.search(r'\\title\{(.*?)\}', line)
            if title:
                output.append('#align(center)[')
                output.append(f'  #text(size: 18pt, weight: "bold")[{title.group(1).replace("\\\\", " ").replace("\\large ", "").replace("\\texttt{", "").replace("}", "")}]')
                output.append(']')
                output.append('')
            continue
        if line.startswith(r'\author{') or line.startswith(r'\date{'):
            continue
            
        # Convert sections
        line = re.sub(r'\\section\{(.*?)\}', r'= \1', line)
        line = re.sub(r'\\subsection\{(.*?)\}', r'== \1', line)
        line = re.sub(r'\\subsubsection\{(.*?)\}', r'=== \1', line)
        
        # Handle lstlisting blocks
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
            output.append(line)
            continue
            
        # Handle definition/theorem/lemma environments
        if r'\begin{definition}' in line:
            output.append('#block(fill: luma(240), inset: 10pt)[')
            continue
        if r'\begin{theorem}' in line or r'\begin{lemma}' in line or r'\begin{instance}' in line:
            output.append('#block(fill: luma(240), inset: 10pt)[')
            continue
        if r'\end{definition}' in line or r'\end{theorem}' in line or r'\end{lemma}' in line or r'\end{instance}' in line:
            output.append(']')
            output.append('')
            continue
            
        # Convert textbf and textit
        line = re.sub(r'\\textbf\{(.*?)\}', r'*\1*', line)
        line = re.sub(r'\\textit\{(.*?)\}', r'_\1_', line)
        line = re.sub(r'\\texttt\{(.*?)\}', r'`\1`', line)
        line = re.sub(r'\\emph\{(.*?)\}', r'_\1_', line)
        
        # Convert math mode (basic)
        line = re.sub(r'\$([^\$]*?)\$', r'$\1$', line)
        
        # Remove LaTeX commands we don't need
        line = line.replace(r'\noindent', '')
        line = line.replace(r'\\', ' ')
        line = line.replace(r'\quad', ' ')
        line = line.replace(r'\qquad', '  ')
        
        # Clean up
        line = line.strip()
        if line or (output and output[-1] != ''):
            output.append(line)
    
    return '\n'.join(output)

def convert_file(input_path):
    """Convert a .tex file to .typ file"""
    
    input_path = Path(input_path)
    output_path = input_path.with_suffix('.typ')
    
    with open(input_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Convert content
    typst_content = convert_tex_to_typst(content)
    
    # Add Typst header
    header = [
        '#set text(font: "New Computer Modern", size: 11pt)',
        '#set page(margin: 1in)',
        '#set heading(numbering: "1.")',
        '',
    ]
    
    final_content = '\n'.join(header) + '\n' + typst_content
    
    # Write output
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(final_content)
    
    print(f"Converted {input_path} to {output_path}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 tex_to_typst.py <tex_file>")
        sys.exit(1)
    
    convert_file(sys.argv[1])