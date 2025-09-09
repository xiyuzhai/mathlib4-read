#!/usr/bin/env python3
"""
Convert LaTeX files to Typst format - simpler version
"""

import re
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
    in_block = False
    
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
            
        # Extract title
        if r'\title{' in line:
            # Extract title content
            title = line[line.find('{') + 1:line.rfind('}')]
            title = title.replace(r'\\', '\n').replace(r'\large ', '').replace(r'\texttt{', '`').replace('}', '')
            output.append('#align(center)[')
            output.append(f'  #text(size: 18pt, weight: "bold")[{title}]')
            output.append(']')
            output.append('')
            continue
            
        # Skip author and date
        if r'\author{' in line or r'\date{' in line:
            continue
            
        # Convert sections
        if r'\section{' in line:
            section = line[line.find('{') + 1:line.rfind('}')]
            output.append(f'= {section}')
            output.append('')
            continue
        if r'\subsection{' in line:
            subsection = line[line.find('{') + 1:line.rfind('}')]
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
            
        # Handle definition/theorem blocks
        if any(env in line for env in [r'\begin{definition}', r'\begin{theorem}', r'\begin{lemma}', r'\begin{instance}']):
            in_block = True
            output.append('')
            continue
        if any(env in line for env in [r'\end{definition}', r'\end{theorem}', r'\end{lemma}', r'\end{instance}']):
            in_block = False
            output.append('')
            continue
            
        # For regular text, just clean up basic formatting
        if line.strip():
            # Replace \textbf{...} with *...*
            line = re.sub(r'\\textbf\{([^}]*)\}', r'*\1*', line)
            # Replace \texttt{...} with `...`
            line = re.sub(r'\\texttt\{([^}]*)\}', r'`\1`', line)
            # Replace \emph{...} with _..._
            line = re.sub(r'\\emph\{([^}]*)\}', r'_\1_', line)
            # Fix math mode - wrap Spec and other functions in quotes
            line = re.sub(r'\$([^$]*?)(Spec|Gamma|Hom|Set|Opens)([^$]*?)\$', r'$\1"\2"\3$', line)
            # Clean up backslashes
            line = line.replace(r'\\', ' ')
            # Remove other LaTeX commands
            line = re.sub(r'\\[a-zA-Z]+\{([^}]*)\}', r'\1', line)
            line = re.sub(r'\\[a-zA-Z]+', '', line)
            
            output.append(line.strip())
        elif output and output[-1] != '':
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