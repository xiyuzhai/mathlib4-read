#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)

// Define a custom code block that preserves formatting
#let leancode(code) = {
  block(
    fill: luma(245),
    inset: 8pt,
    radius: 4pt,
    width: 100%,
    raw(code, lang: "lean", block: true)
  )
}

= Test

Here's how the code should look:

#leancode("theorem of_affine_open_cover {X : Scheme} {P : X.affineOpens → Prop}
  (hP : ∀ (U : X.affineOpens) (f : Γ(X, U)) (hf : X.basicOpen f ≤ U),
    P ⟨X.basicOpen f, (U : X.Opens).isAffineOpen.basicOpen f⟩ →
    P U)
  (hP' : ∀ (U : X.affineOpens) (s : Finset Γ(X, U))
    (hs : Ideal.span (s : Set Γ(X, U)) = ⊤),
    (∀ f : s, P ⟨X.basicOpen f.1, (U : X.Opens).isAffineOpen.basicOpen f⟩) →
    P U)
  (U : X.affineOpens) : P U")

This preserves the indentation and formatting.