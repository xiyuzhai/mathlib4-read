#!/usr/bin/env python3
import os
import re

# Standard literate definitions for Unicode support
LITERATE_DEFS = """  literate={Γ}{{$\\Gamma$}}1
           {⊤}{{$\\top$}}1
           {⟶}{{$\\to$}}2
           {≅}{{$\\cong$}}1
           {⊆}{{$\\subseteq$}}1
           {⨆}{{$\\bigsqcup$}}1
           {∈}{{$\\in$}}1
           {∃}{{$\\exists$}}1
           {∧}{{$\\land$}}1
           {⁻¹}{{$^{-1}$}}2
           {≫}{{>>}}1
           {≤}{{$\\leq$}}1
           {ᵒᵖ}{{$^{op}$}}2
           {⥤}{{$\\Rightarrow$}}2
           {≌}{{$\\simeq$}}1
           {⋙}{{$\\ggg$}}1
           {∀}{{$\\forall$}}1
           {↑}{{$\\uparrow$}}1
           {𝒰}{{$\\mathcal{U}$}}1
           {𝟙}{{$\\mathbb{1}$}}1
           {ι}{{$\\iota$}}1
           {→}{{$\\to$}}1
           {:=}{{$\\mathrel{:=}$}}2
           {×}{{$\\times$}}1
           {⧸}{{$/\\!/$}}1
           {↔}{{$\\leftrightarrow$}}1
           {⟨}{{$\\langle$}}1
           {⟩}{{$\\rangle$}}1
           {α}{{$\\alpha$}}1
           {β}{{$\\beta$}}1
           {γ}{{$\\gamma$}}1
           {δ}{{$\\delta$}}1
           {ε}{{$\\varepsilon$}}1
           {λ}{{$\\lambda$}}1
           {μ}{{$\\mu$}}1
           {σ}{{$\\sigma$}}1
           {τ}{{$\\tau$}}1
           {φ}{{$\\varphi$}}1
           {ψ}{{$\\psi$}}1
           {ω}{{$\\omega$}}1
           {∞}{{$\\infty$}}1
           {∂}{{$\\partial$}}1
           {∇}{{$\\nabla$}}1
           {⤳}{{$\\leadsto$}}1
           {⊓}{{$\\sqcap$}}1
           {⊥}{{$\\bot$}}1
}"""

def fix_tex_file(filepath):
    """Fix a tex file by adding missing closing brace and literate definitions."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check if lstset exists and is properly closed
    if '\\lstset{' in content:
        # Find the lstset block
        lstset_start = content.find('\\lstset{')
        if lstset_start != -1:
            # Look for the end of lstset
            search_area = content[lstset_start:lstset_start+2000] if lstset_start+2000 < len(content) else content[lstset_start:]
            
            # Check if it has literate definitions
            if 'literate=' not in search_area:
                # Find where to insert the literate definitions
                # Look for the comment about Unicode replacements
                unicode_comment = search_area.find('% Unicode replacements')
                if unicode_comment != -1:
                    # Check if there's a closing brace after the comment
                    after_comment = search_area[unicode_comment:]
                    next_section = after_comment.find('\\theoremstyle')
                    if next_section == -1:
                        next_section = after_comment.find('\\newtheorem')
                    if next_section == -1:
                        next_section = after_comment.find('\\title')
                    
                    if next_section != -1:
                        # Check if there's a closing brace between comment and next section
                        closing_brace = after_comment[:next_section].find('}')
                        if closing_brace == -1:
                            # Need to add literate defs and closing brace
                            insertion_point = lstset_start + unicode_comment
                            # Find the end of the comment line
                            newline_after = content[insertion_point:].find('\n')
                            if newline_after != -1:
                                insertion_point += newline_after + 1
                                new_content = content[:insertion_point] + LITERATE_DEFS + '\n' + content[insertion_point:]
                                with open(filepath, 'w', encoding='utf-8') as f:
                                    f.write(new_content)
                                print(f"Fixed {filepath}")
                                return True
    return False

# Get all tex files that need fixing
tex_files = [
    'GammaSpecAdjunction.tex',
    'GluingOneHypercover.tex', 
    'Gluing.tex',
    'Limits.tex',
    'Noetherian.tex',
    'OpenImmersion.tex',
    'Over.tex',
    'Properties.tex',
    'PullbackCarrier.tex',
    'Pullbacks.tex',
    'ResidueField.tex',
    'Restrict.tex',
    'Spec.tex',
    'Stalk.tex',
    'StructureSheaf.tex'
]

for tex_file in tex_files:
    if os.path.exists(tex_file):
        if fix_tex_file(tex_file):
            print(f"Fixed {tex_file}")
        else:
            print(f"Could not fix {tex_file} - may need manual intervention")
    else:
        print(f"File not found: {tex_file}")