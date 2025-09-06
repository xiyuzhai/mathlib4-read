#!/usr/bin/env python3
import glob
import re

def fix_unicode_in_tex(filename):
    """Fix Unicode characters in LaTeX files."""
    
    with open(filename, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    
    # Define replacements for Unicode characters
    # These should be wrapped in $ if not already in math mode
    replacements = [
        # Greek letters
        ('ι', r'$\iota$'),
        ('Γ', r'$\Gamma$'),
        ('α', r'$\alpha$'),
        ('β', r'$\beta$'),
        ('γ', r'$\gamma$'),
        ('δ', r'$\delta$'),
        ('ε', r'$\varepsilon$'),
        ('ζ', r'$\zeta$'),
        ('η', r'$\eta$'),
        ('θ', r'$\theta$'),
        ('κ', r'$\kappa$'),
        ('λ', r'$\lambda$'),
        ('μ', r'$\mu$'),
        ('ν', r'$\nu$'),
        ('ξ', r'$\xi$'),
        ('π', r'$\pi$'),
        ('ρ', r'$\rho$'),
        ('σ', r'$\sigma$'),
        ('τ', r'$\tau$'),
        ('φ', r'$\varphi$'),
        ('χ', r'$\chi$'),
        ('ψ', r'$\psi$'),
        ('ω', r'$\omega$'),
        ('Δ', r'$\Delta$'),
        ('Σ', r'$\Sigma$'),
        ('Π', r'$\Pi$'),
        ('Ω', r'$\Omega$'),
        
        # Mathematical symbols
        ('⟶', r'$\to$'),
        ('→', r'$\to$'),
        ('≅', r'$\cong$'),
        ('≃', r'$\simeq$'),
        ('⊆', r'$\subseteq$'),
        ('⊇', r'$\supseteq$'),
        ('⊂', r'$\subset$'),
        ('⊃', r'$\supset$'),
        ('∈', r'$\in$'),
        ('∉', r'$\notin$'),
        ('∃', r'$\exists$'),
        ('∀', r'$\forall$'),
        ('∧', r'$\land$'),
        ('∨', r'$\lor$'),
        ('≤', r'$\leq$'),
        ('≥', r'$\geq$'),
        ('≠', r'$\neq$'),
        ('≡', r'$\equiv$'),
        ('≈', r'$\approx$'),
        ('∞', r'$\infty$'),
        ('∅', r'$\emptyset$'),
        ('∪', r'$\cup$'),
        ('∩', r'$\cap$'),
        ('×', r'$\times$'),
        ('⊗', r'$\otimes$'),
        ('⊕', r'$\oplus$'),
        ('⊤', r'$\top$'),
        ('⊥', r'$\bot$'),
        ('∘', r'$\circ$'),
        ('∂', r'$\partial$'),
        ('∇', r'$\nabla$'),
        ('∫', r'$\int$'),
        ('∑', r'$\sum$'),
        ('∏', r'$\prod$'),
        ('√', r'$\sqrt{}$'),
        ('⋯', r'$\cdots$'),
        ('↑', r'$\uparrow$'),
        ('↓', r'$\downarrow$'),
        ('↪', r'$\hookrightarrow$'),
        ('⥤', r'$\Rightarrow$'),
        ('≌', r'$\simeq$'),
        ('⋙', r'$\ggg$'),
        ('≫', r'$\gg$'),
        ('≪', r'$\ll$'),
        ('⨆', r'$\bigsqcup$'),
        ('⧸', r'$/\!/$'),
        
        # Special cases with subscripts/superscripts
        ('⁻¹', r'$^{-1}$'),
        ('ᵒᵖ', r'$^{op}$'),
        ('𝒰', r'$\mathcal{U}$'),
        ('𝟙', r'$\mathbb{1}$'),
        ('≃ₜ', r'$\cong_t$'),
        
        # Additional problematic characters
        ('↦', r'$\mapsto$'),
        ('‹', r'$\langle$'),
        ('›', r'$\rangle$'),
        ('⟨', r'$\langle$'),
        ('⟩', r'$\rangle$'),
        ('?_', r'?\_'),
    ]
    
    # Process the content line by line
    lines = content.split('\n')
    in_listing = False
    in_literate = False
    
    for i, line in enumerate(lines):
        # Check if we're entering or leaving a code listing
        if r'\begin{lstlisting}' in line:
            in_listing = True
            continue
        elif r'\end{lstlisting}' in line:
            in_listing = False
            continue
        elif 'literate={' in line:
            in_literate = True
            continue
        elif in_literate and '}' in line:
            # Simple check for end of literate block
            in_literate = False
            continue
            
        # Skip replacements inside code listings and literate blocks
        if in_listing or in_literate:
            continue
            
        # Apply replacements
        for unicode_char, latex_cmd in replacements:
            if unicode_char in line:
                # Check if already in math mode
                # This is a simple heuristic - may need refinement
                if '$' in latex_cmd:
                    # Remove the $ signs if we're already in math mode
                    if re.search(r'\$[^$]*' + re.escape(unicode_char) + r'[^$]*\$', line):
                        # Already in math mode, use just the command
                        line = line.replace(unicode_char, latex_cmd[1:-1])
                    else:
                        # Not in math mode, use with $
                        line = line.replace(unicode_char, latex_cmd)
                else:
                    line = line.replace(unicode_char, latex_cmd)
        
        lines[i] = line
    
    new_content = '\n'.join(lines)
    
    if new_content != original:
        with open(filename, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return True
    return False

# Process all .tex files
tex_files = glob.glob('*.tex')
fixed_files = []

for tex_file in tex_files:
    print(f"Processing {tex_file}...")
    if fix_unicode_in_tex(tex_file):
        fixed_files.append(tex_file)
        print(f"  ✓ Fixed Unicode characters in {tex_file}")
    else:
        print(f"  - No changes needed for {tex_file}")

print(f"\nFixed {len(fixed_files)} files out of {len(tex_files)} total.")