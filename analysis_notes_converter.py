#!/usr/bin/env python3
"""
Convert Lean 4 Analysis modules to LaTeX documentation
"""

import re
import sys
from pathlib import Path

def extract_module_doc(content):
    """Extract the main module documentation from /-! ... -/ blocks"""
    pattern = r'/-!\s*(.*?)\s*-/\s'
    match = re.search(pattern, content, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None

def extract_definitions(content):
    """Extract key definitions from the Lean file"""
    definitions = []
    
    # Extract def statements
    def_pattern = r'^(def|theorem|lemma)\s+(\w+).*?:=\s*(.*?)(?=\n(?:def|theorem|lemma|end|variable|section|\Z))'
    matches = re.finditer(def_pattern, content, re.MULTILINE | re.DOTALL)
    
    for match in matches:
        def_type = match.group(1)
        def_name = match.group(2)
        definitions.append((def_type, def_name))
    
    return definitions

def extract_theorems(content):
    """Extract main theorems and lemmas"""
    theorems = []
    
    # Look for theorem/lemma statements with descriptions
    theorem_pattern = r'/--\s*(.*?)\s*-/\s*\n\s*(theorem|lemma)\s+(\w+)'
    matches = re.finditer(theorem_pattern, content, re.MULTILINE)
    
    for match in matches:
        description = match.group(1).strip()
        theorem_type = match.group(2)
        theorem_name = match.group(3)
        theorems.append((theorem_name, description))
    
    return theorems

def lean_to_latex(lean_expr):
    """Convert Lean notation to LaTeX"""
    # Basic replacements
    replacements = {
        r'𝕜': r'\mathbb{K}',
        r'ℝ': r'\mathbb{R}',
        r'ℂ': r'\mathbb{C}',
        r'ℕ': r'\mathbb{N}',
        r'ℤ': r'\mathbb{Z}',
        r'→': r'\to',
        r'↦': r'\mapsto',
        r'∀': r'\forall',
        r'∃': r'\exists',
        r'∈': r'\in',
        r'∉': r'\notin',
        r'⊆': r'\subseteq',
        r'⊂': r'\subset',
        r'∪': r'\cup',
        r'∩': r'\cap',
        r'×': r'\times',
        r'⁻¹': r'^{-1}',
        r'∞': r'\infty',
        r'·': r'\cdot',
        r'∘': r'\circ',
        r'≤': r'\leq',
        r'≥': r'\geq',
        r'≠': r'\neq',
        r'∂': r'\partial',
        r'∇': r'\nabla',
        r'∫': r'\int',
        r'∑': r'\sum',
        r'∏': r'\prod',
        r'lim': r'\lim',
        r'sup': r'\sup',
        r'inf': r'\inf',
        r'𝓝': r'\mathcal{N}',
        r'𝓤': r'\mathcal{U}',
        r'𝓕': r'\mathcal{F}',
    }
    
    result = lean_expr
    for lean, latex in replacements.items():
        result = result.replace(lean, latex)
    
    # Handle derivatives
    result = re.sub(r'deriv\s+(\w+)', r"\\frac{d}{dx}\\left(\\1\\right)", result)
    result = re.sub(r'fderiv\s+(\w+)', r"D\\1", result)
    result = re.sub(r'HasDerivAt\s+(\w+)\s+(\w+)\s+(\w+)', r"\\1'(\\3) = \\2", result)
    
    return result

def convert_file(input_path, output_path):
    """Convert a Lean file to LaTeX documentation"""
    
    with open(input_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Extract file name without extension
    module_name = Path(input_path).stem
    
    # Start LaTeX document
    latex = [
        f"\\documentclass{{article}}",
        f"\\usepackage{{amsmath, amssymb, amsthm}}",
        f"\\usepackage{{hyperref}}",
        f"\\usepackage{{listings}}",
        f"\\usepackage{{xcolor}}",
        f"",
        f"\\theoremstyle{{definition}}",
        f"\\newtheorem{{definition}}{{Definition}}",
        f"\\newtheorem{{theorem}}{{Theorem}}",
        f"\\newtheorem{{lemma}}{{Lemma}}",
        f"\\newtheorem{{example}}{{Example}}",
        f"",
        f"\\title{{Analysis Module: {module_name}}}",
        f"\\author{{Mathlib4 Documentation}}",
        f"\\date{{\\today}}",
        f"",
        f"\\begin{{document}}",
        f"\\maketitle",
        f""
    ]
    
    # Add module documentation
    module_doc = extract_module_doc(content)
    if module_doc:
        latex.append("\\section{Module Overview}")
        # Convert markdown-style headers to LaTeX
        module_doc = re.sub(r'^#\s+(.+?)$', r'\\subsection{\1}', module_doc, flags=re.MULTILINE)
        module_doc = re.sub(r'^##\s+(.+?)$', r'\\subsubsection{\1}', module_doc, flags=re.MULTILINE)
        # Convert code blocks
        module_doc = re.sub(r'```lean\s*(.*?)\s*```', r'\\begin{lstlisting}[language=lean]\n\1\n\\end{lstlisting}', module_doc, flags=re.DOTALL)
        # Convert inline code - be more careful with escaping
        module_doc = re.sub(r'`([^`]+)`', lambda m: r'\\texttt{' + m.group(1).replace('\\', r'\\textbackslash ').replace('{', r'\\{').replace('}', r'\\}').replace('_', r'\\_').replace('#', r'\\#').replace('&', r'\\&').replace('%', r'\\%').replace('$', r'\\$') + '}', module_doc)
        # Convert basic Lean notation
        module_doc = lean_to_latex(module_doc)
        # Fix any remaining issues
        module_doc = module_doc.replace(r'\1', '').replace(r'\2', '').replace(r'\3', '')
        latex.append(module_doc)
        latex.append("")
    
    # Add main definitions section
    definitions = extract_definitions(content)
    if definitions:
        latex.append("\\section{Key Definitions}")
        for def_type, def_name in definitions[:10]:  # Limit to first 10
            latex.append(f"\\begin{{definition}}[{def_name}]")
            latex.append(f"A {def_type} defining \\texttt{{{def_name}}}")
            latex.append(f"\\end{{definition}}")
            latex.append("")
    
    # Add theorems section
    theorems = extract_theorems(content)
    if theorems:
        latex.append("\\section{Main Theorems}")
        for theorem_name, description in theorems[:10]:  # Limit to first 10
            latex.append(f"\\begin{{theorem}}[{theorem_name}]")
            latex.append(lean_to_latex(description))
            latex.append(f"\\end{{theorem}}")
            latex.append("")
    
    # Extract specific derivative-related content if present
    if 'deriv' in content.lower() or 'derivative' in content.lower():
        latex.append("\\section{Derivatives}")
        latex.append("This module deals with derivatives of functions $f : \\mathbb{K} \\to F$ where:")
        latex.append("\\begin{itemize}")
        latex.append("\\item $\\mathbb{K}$ is a normed field")
        latex.append("\\item $F$ is a normed space over $\\mathbb{K}$")
        latex.append("\\end{itemize}")
        latex.append("")
        
        # Add derivative notations
        latex.append("\\subsection{Notations}")
        latex.append("\\begin{itemize}")
        latex.append("\\item $\\text{deriv } f$ denotes the derivative of $f$")
        latex.append("\\item $\\text{HasDerivAt } f \\, f' \\, x$ means $f'(x) = f'$")
        latex.append("\\item $\\text{derivWithin } f \\, s \\, x$ is the derivative within set $s$")
        latex.append("\\end{itemize}")
        latex.append("")
    
    # Close document
    latex.extend([
        "",
        "\\end{document}"
    ])
    
    # Write output
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(latex))
    
    print(f"Converted {input_path} to {output_path}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 analysis_notes_converter.py <lean_file>")
        sys.exit(1)
    
    input_file = sys.argv[1]
    # Use parent directory name + stem for unique naming
    input_path = Path(input_file)
    if input_path.parent.name != '.':
        output_file = f"{input_path.parent.name}_{input_path.stem}_notes.tex"
    else:
        output_file = f"{input_path.stem}_notes.tex"
    
    convert_file(input_file, output_file)