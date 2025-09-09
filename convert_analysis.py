#!/usr/bin/env python3
"""
Convert Lean 4 Analysis modules to compilable LaTeX documentation
"""

import re
import sys
from pathlib import Path

def extract_module_doc(content):
    """Extract the main module documentation from /-! ... -/ blocks"""
    pattern = r'/-!\s*(.*?)\s*-/'
    match = re.search(pattern, content, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None

def convert_file(input_path):
    """Convert a Lean file to LaTeX documentation in the same directory"""
    
    input_path = Path(input_path)
    # Ensure we're working with absolute path
    if not input_path.is_absolute():
        input_path = Path.cwd() / input_path
    output_path = input_path.with_suffix('.tex')
    
    with open(input_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    module_name = input_path.stem
    
    # Start LaTeX document - using verbatim for Unicode preservation
    latex = [
        r"\documentclass{article}",
        r"\usepackage[utf8]{inputenc}",
        r"\usepackage{amsmath, amssymb, amsthm}",
        r"\usepackage{listings}",
        r"\usepackage{xcolor}",
        r"\usepackage{geometry}",
        r"\geometry{margin=1in}",
        r"",
        r"\theoremstyle{definition}",
        r"\newtheorem{definition}{Definition}",
        r"\newtheorem{theorem}{Theorem}",
        r"",
        r"\title{Analysis Module: " + module_name.replace('_', r'\_') + r"}",
        r"\author{Mathlib4 Documentation}",
        r"\date{\today}",
        r"",
        r"\begin{document}",
        r"\maketitle",
        r""
    ]
    
    # Add module documentation
    module_doc = extract_module_doc(content)
    if module_doc:
        latex.append(r"\section{Module Overview}")
        latex.append(r"\begin{verbatim}")
        
        # Add the documentation as-is to preserve Unicode
        lines = module_doc.split('\n')
        for line in lines[:50]:  # Limit to first 50 lines
            latex.append(line)
        
        latex.append(r"\end{verbatim}")
        latex.append("")
    
    # Extract some key definitions
    latex.append(r"\section{Key Definitions}")
    latex.append(r"\begin{verbatim}")
    
    # Find def/theorem/lemma statements
    def_pattern = r'^(def|theorem|lemma)\s+(\w+)'
    matches = re.finditer(def_pattern, content, re.MULTILINE)
    
    count = 0
    for match in matches:
        if count >= 10:  # Limit to first 10
            break
        def_type = match.group(1)
        def_name = match.group(2)
        latex.append(f"{def_type} {def_name}")
        count += 1
    
    latex.append(r"\end{verbatim}")
    
    # Close document
    latex.extend([
        "",
        r"\end{document}"
    ])
    
    # Write output
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(latex))
    
    print(f"Created {output_path}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 convert_analysis.py <lean_file>")
        sys.exit(1)
    
    convert_file(sys.argv[1])