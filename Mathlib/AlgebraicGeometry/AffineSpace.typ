#set document(title: "Affine Space")
#set heading(numbering: "1.")

= Affine Space

== Overview

Defines affine space $𝔸(n; S)$ over a scheme $S$ and morphisms into it.

== Main Definitions

=== Affine Space

`AffineSpace (n : Type v) (S : Scheme)`: The affine $n$-space over $S$
- Defined as pullback of terminal morphisms from $S$ and $"Spec" ℤ[n]$
- Notation: `𝔸(n; S)`
- Note: $n$ is an arbitrary index type (e.g., `Fin m`)

=== Canonical Structure

`AffineSpace.over`: Instance making $𝔸(n; S)$ canonically over $S$
- `hom := pullback.fst`

`AffineSpace.toSpecMvPoly`: Map $𝔸(n; S) → "Spec" ℤ[n]$
- Given by `pullback.snd`

== Coordinate Functions

=== Standard Coordinates

`AffineSpace.coord`: The standard coordinate functions on affine space
- `coord i`: The $i$-th coordinate function
- Global sections of the structure sheaf

== Morphisms into Affine Space

=== Vector of Functions

`AffineSpace.homOfVector`: Constructs morphism $X → 𝔸(n; S)$
- Input: Morphism $X → S$ and $n$ coordinate functions on $X$
- Output: The corresponding morphism to affine space

=== Equivalence for Morphisms

`AffineSpace.toSpecMvPolyIntEquiv`:
- Morphisms $X → "Spec" ℤ[n]$ ≃ $n$-tuples of global sections
- `toFun`: Extracts coordinates via $Γ$-Spec adjunction
- `invFun`: Constructs morphism via evaluation

`AffineSpace.homOverEquiv`: For $X$ over $S$
- $S$-morphisms $X → 𝔸(n; S)$ ≃ $n$-tuples of global sections
- Combines pullback structure with `toSpecMvPolyIntEquiv`

== Isomorphisms

=== Affine Space over Spec

`AffineSpace.SpecIso`: $𝔸(n; "Spec" R) ≅ "Spec" R[n]$
- Natural isomorphism
- Identifies affine space over affine base with polynomial ring spectrum

== Properties

=== Finiteness

`AffineSpace.finite`: The projection $𝔸(n; S) → S$ is finite when $n$ is finite

`AffineSpace.finitePresentation`: The projection is of finite presentation when $n$ is finite

=== Universal Property

The affine space satisfies the universal property:
- Morphisms into $𝔸(n; S)$ over $S$ correspond to $n$-tuples of functions
- This makes it the scheme-theoretic product $𝔸^1 × ... × 𝔸^1$ ($n$ times)

== Implementation Notes

- Uses `MvPolynomial n (ULift ℤ)` for universe polymorphism
- Local notation: `ℤ[n]` for the polynomial ring
- Universe parameters carefully managed for pullback construction
- Equivalences use `Equiv` for computational content
