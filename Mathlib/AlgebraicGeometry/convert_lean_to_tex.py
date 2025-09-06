#!/usr/bin/env python3
"""
Convert Lean 4 files to LaTeX format for documentation purposes.
"""
import sys
import os
import re

def convert_lean_to_tex(lean_file):
    """Convert a .lean file to .tex format"""
    
    # Read the lean file
    with open(lean_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Extract the base name
    base_name = os.path.splitext(os.path.basename(lean_file))[0]
    
    # Start building the LaTeX document
    tex_content = r"""\documentclass{article}
\input{unicode_preamble}

\usepackage{xcolor}
\usepackage{listings}
\usepackage{hyperref}
\usepackage{geometry}
\geometry{margin=1in}

% Define colors for Lean syntax highlighting
\definecolor{leanKeyword}{RGB}{0, 0, 255}       % Blue for keywords
\definecolor{leanType}{RGB}{139, 0, 139}        % Dark magenta for types
\definecolor{leanString}{RGB}{0, 128, 0}        % Green for strings
\definecolor{leanComment}{RGB}{128, 128, 128}   % Gray for comments
\definecolor{leanDefinition}{RGB}{255, 140, 0}  % Dark orange for definitions

% Configure listings for Lean
\lstdefinelanguage{Lean}{
    keywords={def, theorem, lemma, example, axiom, class, instance, inductive, structure,
              variable, namespace, open, import, export, section, end, if, then, else,
              match, with, fun, let, have, show, by, where, do, return, for, in,
              variable, universe, noncomputable, partial, mutual, protected, private,
              unsafe, opaque, @[simp], @[inline], @[reducible], @[irreducible],
              attribute, set_option, notation, infixl, infixr, prefix, postfix,
              scoped, local, macro, syntax, elab, deriving, extends, mk},
    morekeys={Type, Prop, Sort, Nat, Int, Real, Bool, true, false, Unit, 
              List, Array, Option, some, none, Sum, Prod, Sigma, Pi,
              and, or, not, iff, exists, forall},
    sensitive=true,
    morecomment=[l]{--},
    morecomment=[s]{/-}{-/},
    morestring=[b]",
    morestring=[b]',
}

\lstset{
    language=Lean,
    basicstyle=\ttfamily\small,
    keywordstyle=\color{leanKeyword}\bfseries,
    commentstyle=\color{leanComment}\itshape,
    stringstyle=\color{leanString},
    numberstyle=\tiny\color{gray},
    numbers=left,
    stepnumber=1,
    numbersep=5pt,
    backgroundcolor=\color{white},
    frame=single,
    rulecolor=\color{black!30},
    breaklines=true,
    breakatwhitespace=true,
    tabsize=2,
    captionpos=b,
    showstringspaces=false,
    literate={
        {α}{{$\alpha$}}1 {β}{{$\beta$}}1 {γ}{{$\gamma$}}1 {δ}{{$\delta$}}1
        {ε}{{$\varepsilon$}}1 {ζ}{{$\zeta$}}1 {η}{{$\eta$}}1 {θ}{{$\theta$}}1
        {ι}{{$\iota$}}1 {κ}{{$\kappa$}}1 {λ}{{$\lambda$}}1 {μ}{{$\mu$}}1
        {ν}{{$\nu$}}1 {ξ}{{$\xi$}}1 {π}{{$\pi$}}1 {ρ}{{$\rho$}}1
        {σ}{{$\sigma$}}1 {τ}{{$\tau$}}1 {φ}{{$\varphi$}}1 {χ}{{$\chi$}}1
        {ψ}{{$\psi$}}1 {ω}{{$\omega$}}1 {Γ}{{$\Gamma$}}1 {Δ}{{$\Delta$}}1
        {Θ}{{$\Theta$}}1 {Λ}{{$\Lambda$}}1 {Σ}{{$\Sigma$}}1 {Φ}{{$\Phi$}}1
        {Ψ}{{$\Psi$}}1 {Ω}{{$\Omega$}}1
        {→}{{$\rightarrow$}}2 {←}{{$\leftarrow$}}2 {⟶}{{$\longrightarrow$}}2
        {↔}{{$\leftrightarrow$}}2 {⟷}{{$\longleftrightarrow$}}2
        {≤}{{$\leq$}}1 {≥}{{$\geq$}}1 {≠}{{$\neq$}}1 {≈}{{$\approx$}}1
        {≡}{{$\equiv$}}1 {≅}{{$\cong$}}1 {≃}{{$\simeq$}}1
        {∈}{{$\in$}}1 {∉}{{$\notin$}}1 {⊆}{{$\subseteq$}}1 {⊇}{{$\supseteq$}}1
        {⊂}{{$\subset$}}1 {⊃}{{$\supset$}}1 {∪}{{$\cup$}}1 {∩}{{$\cap$}}1
        {∅}{{$\emptyset$}}1 {∞}{{$\infty$}}1 {∂}{{$\partial$}}1
        {∀}{{$\forall$}}1 {∃}{{$\exists$}}1 {∧}{{$\land$}}1 {∨}{{$\lor$}}1
        {¬}{{$\neg$}}1 {⊤}{{$\top$}}1 {⊥}{{$\bot$}}1
        {×}{{$\times$}}1 {·}{{$\cdot$}}1 {∘}{{$\circ$}}1
        {⊗}{{$\otimes$}}1 {⊕}{{$\oplus$}}1 {⊙}{{$\odot$}}1
        {∑}{{$\sum$}}1 {∏}{{$\prod$}}1 {∫}{{$\int$}}1
        {₀}{{$_0$}}1 {₁}{{$_1$}}1 {₂}{{$_2$}}1 {₃}{{$_3$}}1 {₄}{{$_4$}}1
        {₅}{{$_5$}}1 {₆}{{$_6$}}1 {₇}{{$_7$}}1 {₈}{{$_8$}}1 {₉}{{$_9$}}1
        {ₙ}{{$_n$}}1 {ₘ}{{$_m$}}1 {ᵢ}{{$_i$}}1 {ⱼ}{{$_j$}}1
        {⁰}{{$^0$}}1 {¹}{{$^1$}}1 {²}{{$^2$}}1 {³}{{$^3$}}1 {⁴}{{$^4$}}1
        {⁵}{{$^5$}}1 {⁶}{{$^6$}}1 {⁷}{{$^7$}}1 {⁸}{{$^8$}}1 {⁹}{{$^9$}}1
        {ⁿ}{{$^n$}}1 {ᵐ}{{$^m$}}1 {ⁱ}{{$^i$}}1
        {ℕ}{{$\mathbb{N}$}}1 {ℤ}{{$\mathbb{Z}$}}1 {ℚ}{{$\mathbb{Q}$}}1
        {ℝ}{{$\mathbb{R}$}}1 {ℂ}{{$\mathbb{C}$}}1
        {𝒰}{{$\mathcal{U}$}}1 {𝒱}{{$\mathcal{V}$}}1 {𝒲}{{$\mathcal{W}$}}1
        {𝒳}{{$\mathcal{X}$}}1 {𝒴}{{$\mathcal{Y}$}}1 {𝒵}{{$\mathcal{Z}$}}1
        {𝔸}{{$\mathbb{A}$}}1 {𝔹}{{$\mathbb{B}$}}1 {𝔽}{{$\mathbb{F}$}}1
        {𝕂}{{$\mathbb{K}$}}1 {𝕊}{{$\mathbb{S}$}}1
        {⟨}{{$\langle$}}1 {⟩}{{$\rangle$}}1 {⌊}{{$\lfloor$}}1 {⌋}{{$\rfloor$}}1
        {⌈}{{$\lceil$}}1 {⌉}{{$\rceil$}}1
        {⁻¹}{{$^{-1}$}}2 {▸}{{$\triangleright$}}1
    }
}

"""
    
    # Add title and author
    tex_content += f"""\\title{{Lean 4 Code: {base_name}}}
\\author{{Mathlib4}}
\\date{{\\today}}

\\begin{{document}}
\\maketitle

\\section{{Source Code}}

The following is the Lean 4 source code from \\texttt{{{base_name}.lean}}:

\\begin{{lstlisting}}[language=Lean, caption={{{base_name}.lean}}]
{content}
\\end{{lstlisting}}

\\end{{document}}
"""
    
    return tex_content

def main():
    if len(sys.argv) != 2:
        print("Usage: python convert_lean_to_tex.py <file.lean>")
        sys.exit(1)
    
    lean_file = sys.argv[1]
    
    if not os.path.exists(lean_file):
        print(f"Error: File {lean_file} not found")
        sys.exit(1)
    
    if not lean_file.endswith('.lean'):
        print("Error: Input file must be a .lean file")
        sys.exit(1)
    
    # Generate output filename
    base_name = os.path.splitext(lean_file)[0]
    tex_file = base_name + '.tex'
    
    # Convert the file
    tex_content = convert_lean_to_tex(lean_file)
    
    # Write the output
    with open(tex_file, 'w', encoding='utf-8') as f:
        f.write(tex_content)
    
    print(f"Successfully converted {lean_file} to {tex_file}")

if __name__ == "__main__":
    main()