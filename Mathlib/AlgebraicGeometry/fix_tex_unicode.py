#!/usr/bin/env python3
import glob
import re

def fix_tex_with_unicode(filename):
    """Update LaTeX files to properly handle Unicode characters."""
    
    with open(filename, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    
    # Check if file already has newunicodechar package
    has_newunicodechar = 'newunicodechar' in content
    
    if not has_newunicodechar:
        # Add necessary packages after \usepackage[utf8]{inputenc}
        unicode_packages = r"""% Better Unicode support
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{textcomp}
\usepackage{newunicodechar}
\usepackage{stmaryrd}

% Define Unicode characters
\newunicodechar{↦}{\ensuremath{\mapsto}}
\newunicodechar{⟨}{\ensuremath{\langle}}
\newunicodechar{⟩}{\ensuremath{\rangle}}
\newunicodechar{‹}{\ensuremath{\langle}}
\newunicodechar{›}{\ensuremath{\rangle}}
\newunicodechar{→}{\ensuremath{\to}}
\newunicodechar{⟶}{\ensuremath{\longrightarrow}}
\newunicodechar{↪}{\ensuremath{\hookrightarrow}}
\newunicodechar{≅}{\ensuremath{\cong}}
\newunicodechar{≃}{\ensuremath{\simeq}}
\newunicodechar{⊆}{\ensuremath{\subseteq}}
\newunicodechar{⊇}{\ensuremath{\supseteq}}
\newunicodechar{∈}{\ensuremath{\in}}
\newunicodechar{∉}{\ensuremath{\notin}}
\newunicodechar{∃}{\ensuremath{\exists}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{∧}{\ensuremath{\land}}
\newunicodechar{∨}{\ensuremath{\lor}}
\newunicodechar{≤}{\ensuremath{\leq}}
\newunicodechar{≥}{\ensuremath{\geq}}
\newunicodechar{≠}{\ensuremath{\neq}}
\newunicodechar{≡}{\ensuremath{\equiv}}
\newunicodechar{≈}{\ensuremath{\approx}}
\newunicodechar{∞}{\ensuremath{\infty}}
\newunicodechar{∅}{\ensuremath{\emptyset}}
\newunicodechar{∪}{\ensuremath{\cup}}
\newunicodechar{∩}{\ensuremath{\cap}}
\newunicodechar{×}{\ensuremath{\times}}
\newunicodechar{⊗}{\ensuremath{\otimes}}
\newunicodechar{⊕}{\ensuremath{\oplus}}
\newunicodechar{⊤}{\ensuremath{\top}}
\newunicodechar{⊥}{\ensuremath{\bot}}
\newunicodechar{∘}{\ensuremath{\circ}}
\newunicodechar{∂}{\ensuremath{\partial}}
\newunicodechar{∇}{\ensuremath{\nabla}}
\newunicodechar{∫}{\ensuremath{\int}}
\newunicodechar{∑}{\ensuremath{\sum}}
\newunicodechar{∏}{\ensuremath{\prod}}
\newunicodechar{⋯}{\ensuremath{\cdots}}
\newunicodechar{⨆}{\ensuremath{\bigsqcup}}
\newunicodechar{⧸}{\ensuremath{/}}
\newunicodechar{≫}{\ensuremath{\gg}}
\newunicodechar{≪}{\ensuremath{\ll}}
\newunicodechar{⥤}{\ensuremath{\Rightarrow}}
\newunicodechar{⋙}{\ensuremath{\ggg}}
\newunicodechar{≌}{\ensuremath{\fallingdotseq}}
\newunicodechar{↑}{\ensuremath{\uparrow}}
\newunicodechar{↓}{\ensuremath{\downarrow}}
\newunicodechar{⇒}{\ensuremath{\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\Leftarrow}}
\newunicodechar{⇔}{\ensuremath{\Leftrightarrow}}
\newunicodechar{↔}{\ensuremath{\leftrightarrow}}
\newunicodechar{⊢}{\ensuremath{\vdash}}
\newunicodechar{⊣}{\ensuremath{\dashv}}
\newunicodechar{⊓}{\ensuremath{\sqcap}}
\newunicodechar{⊔}{\ensuremath{\sqcup}}
\newunicodechar{⋮}{\ensuremath{\vdots}}
\newunicodechar{⋱}{\ensuremath{\ddots}}
\newunicodechar{√}{\ensuremath{\sqrt{}}}
\newunicodechar{∝}{\ensuremath{\propto}}
\newunicodechar{∼}{\ensuremath{\sim}}
\newunicodechar{≲}{\ensuremath{\lesssim}}
\newunicodechar{≳}{\ensuremath{\gtrsim}}
\newunicodechar{⊂}{\ensuremath{\subset}}
\newunicodechar{⊃}{\ensuremath{\supset}}
\newunicodechar{⊊}{\ensuremath{\subsetneq}}
\newunicodechar{⊋}{\ensuremath{\supsetneq}}
\newunicodechar{∖}{\ensuremath{\setminus}}
\newunicodechar{∣}{\ensuremath{\mid}}
\newunicodechar{∤}{\ensuremath{\nmid}}
\newunicodechar{∥}{\ensuremath{\parallel}}
\newunicodechar{∦}{\ensuremath{\nparallel}}
\newunicodechar{⊙}{\ensuremath{\odot}}
\newunicodechar{⊖}{\ensuremath{\ominus}}
\newunicodechar{⊘}{\ensuremath{\oslash}}
\newunicodechar{⊚}{\ensuremath{\circledcirc}}
\newunicodechar{⊛}{\ensuremath{\circledast}}
\newunicodechar{⊝}{\ensuremath{\circleddash}}
\newunicodechar{◯}{\ensuremath{\bigcirc}}
\newunicodechar{⬝}{\ensuremath{\cdot}}
\newunicodechar{▸}{\ensuremath{\blacktriangleright}}

% Greek letters
\newunicodechar{α}{\ensuremath{\alpha}}
\newunicodechar{β}{\ensuremath{\beta}}
\newunicodechar{γ}{\ensuremath{\gamma}}
\newunicodechar{δ}{\ensuremath{\delta}}
\newunicodechar{ε}{\ensuremath{\varepsilon}}
\newunicodechar{ζ}{\ensuremath{\zeta}}
\newunicodechar{η}{\ensuremath{\eta}}
\newunicodechar{θ}{\ensuremath{\theta}}
\newunicodechar{ι}{\ensuremath{\iota}}
\newunicodechar{κ}{\ensuremath{\kappa}}
\newunicodechar{λ}{\ensuremath{\lambda}}
\newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{ν}{\ensuremath{\nu}}
\newunicodechar{ξ}{\ensuremath{\xi}}
\newunicodechar{π}{\ensuremath{\pi}}
\newunicodechar{ρ}{\ensuremath{\rho}}
\newunicodechar{σ}{\ensuremath{\sigma}}
\newunicodechar{τ}{\ensuremath{\tau}}
\newunicodechar{φ}{\ensuremath{\varphi}}
\newunicodechar{χ}{\ensuremath{\chi}}
\newunicodechar{ψ}{\ensuremath{\psi}}
\newunicodechar{ω}{\ensuremath{\omega}}
\newunicodechar{Γ}{\ensuremath{\Gamma}}
\newunicodechar{Δ}{\ensuremath{\Delta}}
\newunicodechar{Σ}{\ensuremath{\Sigma}}
\newunicodechar{Π}{\ensuremath{\Pi}}
\newunicodechar{Ω}{\ensuremath{\Omega}}

% Superscripts and subscripts  
\newunicodechar{⁻}{\ensuremath{^{-}}}
\newunicodechar{¹}{\ensuremath{^{1}}}
\newunicodechar{²}{\ensuremath{^{2}}}
\newunicodechar{³}{\ensuremath{^{3}}}
\newunicodechar{⁴}{\ensuremath{^{4}}}
\newunicodechar{⁵}{\ensuremath{^{5}}}
\newunicodechar{⁶}{\ensuremath{^{6}}}
\newunicodechar{⁷}{\ensuremath{^{7}}}
\newunicodechar{⁸}{\ensuremath{^{8}}}
\newunicodechar{⁹}{\ensuremath{^{9}}}
\newunicodechar{⁰}{\ensuremath{^{0}}}
\newunicodechar{ⁿ}{\ensuremath{^{n}}}
\newunicodechar{ᵒ}{\ensuremath{^{o}}}
\newunicodechar{ᵖ}{\ensuremath{^{p}}}
\newunicodechar{ᵐ}{\ensuremath{^{m}}}
\newunicodechar{ᵢ}{\ensuremath{_{i}}}
\newunicodechar{₀}{\ensuremath{_{0}}}
\newunicodechar{₁}{\ensuremath{_{1}}}
\newunicodechar{₂}{\ensuremath{_{2}}}
\newunicodechar{₃}{\ensuremath{_{3}}}
\newunicodechar{₄}{\ensuremath{_{4}}}
\newunicodechar{₅}{\ensuremath{_{5}}}
\newunicodechar{₆}{\ensuremath{_{6}}}
\newunicodechar{₇}{\ensuremath{_{7}}}
\newunicodechar{₈}{\ensuremath{_{8}}}
\newunicodechar{₉}{\ensuremath{_{9}}}
\newunicodechar{ₙ}{\ensuremath{_{n}}}
\newunicodechar{ₘ}{\ensuremath{_{m}}}

% Mathematical alphabets
\newunicodechar{𝒰}{\ensuremath{\mathcal{U}}}
\newunicodechar{𝒱}{\ensuremath{\mathcal{V}}}
\newunicodechar{𝒲}{\ensuremath{\mathcal{W}}}
\newunicodechar{𝒳}{\ensuremath{\mathcal{X}}}
\newunicodechar{𝒴}{\ensuremath{\mathcal{Y}}}
\newunicodechar{𝒵}{\ensuremath{\mathcal{Z}}}
\newunicodechar{𝓐}{\ensuremath{\mathcal{A}}}
\newunicodechar{𝓑}{\ensuremath{\mathcal{B}}}
\newunicodechar{𝓒}{\ensuremath{\mathcal{C}}}
\newunicodechar{𝓓}{\ensuremath{\mathcal{D}}}
\newunicodechar{𝓔}{\ensuremath{\mathcal{E}}}
\newunicodechar{𝓕}{\ensuremath{\mathcal{F}}}
\newunicodechar{𝓖}{\ensuremath{\mathcal{G}}}
\newunicodechar{𝓗}{\ensuremath{\mathcal{H}}}
\newunicodechar{𝓘}{\ensuremath{\mathcal{I}}}
\newunicodechar{𝓙}{\ensuremath{\mathcal{J}}}
\newunicodechar{𝓚}{\ensuremath{\mathcal{K}}}
\newunicodechar{𝓛}{\ensuremath{\mathcal{L}}}
\newunicodechar{𝓜}{\ensuremath{\mathcal{M}}}
\newunicodechar{𝓝}{\ensuremath{\mathcal{N}}}
\newunicodechar{𝓞}{\ensuremath{\mathcal{O}}}
\newunicodechar{𝓟}{\ensuremath{\mathcal{P}}}
\newunicodechar{𝓠}{\ensuremath{\mathcal{Q}}}
\newunicodechar{𝓡}{\ensuremath{\mathcal{R}}}
\newunicodechar{𝓢}{\ensuremath{\mathcal{S}}}
\newunicodechar{𝓣}{\ensuremath{\mathcal{T}}}
\newunicodechar{𝟙}{\ensuremath{\mathbb{1}}}
\newunicodechar{𝟘}{\ensuremath{\mathbb{0}}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathbb{Q}}}
\newunicodechar{ℝ}{\ensuremath{\mathbb{R}}}
\newunicodechar{ℂ}{\ensuremath{\mathbb{C}}}

"""
        
        # Find where to insert the packages
        # Look for \usepackage{amsmath or similar early package declaration
        pattern = r'(\\usepackage\[utf8\]\{inputenc\})'
        if re.search(pattern, content):
            # Use a lambda to avoid issues with backslashes
            content = re.sub(pattern, lambda m: m.group(1) + '\n' + unicode_packages, content, count=1)
        else:
            # If not found, add after documentclass
            pattern = r'(\\documentclass.*?\n)'
            content = re.sub(pattern, lambda m: m.group(1) + '\\usepackage[utf8]{inputenc}\n' + unicode_packages, content, count=1)
    
    # Remove the old literate block if it exists (it's not needed with newunicodechar)
    # Find and remove the literate block in lstdefinelanguage
    pattern = r'(%\s*Unicode replacements.*?literate=\{[^}]*\}[^}]*\})'
    content = re.sub(pattern, '', content, flags=re.DOTALL)
    
    # Also clean up any lines that have just "literate={...}" 
    pattern = r'\s*literate=\{[^}]*\}[^,\n]*,?\n'
    content = re.sub(pattern, '\n', content)
    
    if content != original:
        with open(filename, 'w', encoding='utf-8') as f:
            f.write(content)
        return True
    return False

# Process all .tex files except test_simple.tex
tex_files = [f for f in glob.glob('*.tex') if f != 'test_simple.tex']
fixed_files = []

for tex_file in tex_files:
    print(f"Processing {tex_file}...")
    if fix_tex_with_unicode(tex_file):
        fixed_files.append(tex_file)
        print(f"  ✓ Updated {tex_file} with proper Unicode support")
    else:
        print(f"  - No changes needed for {tex_file}")

print(f"\nFixed {len(fixed_files)} files out of {len(tex_files)} total.")