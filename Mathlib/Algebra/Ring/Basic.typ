#set document(title: "Ring Basic Lemmas")
#set heading(numbering: "1.")

= Ring Basic Lemmas

== Overview

Lemmas about semirings, rings and domains, focusing on the interaction between `+` and `*`. Definitions are in `Algebra.Ring.Defs`.

== AddHom Multiplication

=== Left and Right Multiplication

`AddHom.mulLeft [Distrib R] (r : R)`: Left multiplication by `r` as additive homomorphism
- `toFun := (r * ·)`
- Preserves addition: `r * (a + b) = r * a + r * b`

`AddHom.mulRight [Distrib R] (r : R)`: Right multiplication by `r` as additive homomorphism
- `toFun := (· * r)`
- Preserves addition: `(a + b) * r = a * r + b * r`

== AddMonoidHom Multiplication

=== Basic Multiplication Homomorphisms

`AddMonoidHom.mulLeft (r : R)`: Left multiplication in semirings
- Maps zero: `r * 0 = 0`
- Maps addition: `r * (a + b) = r * a + r * b`

`AddMonoidHom.mulRight (r : R)`: Right multiplication in semirings
- Maps zero: `0 * r = 0`
- Maps addition: `(a + b) * r = a * r + b * r`

=== Bilinear Multiplication

`AddMonoidHom.mul : R →+ R →+ R`: Multiplication as additive homomorphism in both arguments
- First argument: `mul x` gives left multiplication by `x`
- Curried form makes multiplication bilinear

=== Preservation Lemmas

`map_mul_iff`: Characterizes when `f : R →+ S` preserves multiplication
- `(∀ x y, f (x * y) = f x * f y)` iff composition with `mul` commutes

`mulLeft_eq_mulRight_iff_forall_commute`: 
- `mulLeft a = mulRight a` iff `a` commutes with everything

== AddMonoid.End Multiplication

=== Endomorphism Multiplication

`AddMonoid.End.mulLeft : R →+ AddMonoid.End R`: 
- Sends `a` to the endomorphism of left multiplication by `a`

`AddMonoid.End.mulRight : R →+ AddMonoid.End R`:
- Sends `a` to the endomorphism of right multiplication by `a`

=== Commutativity

`mulRight_eq_mulLeft` [NonUnitalNonAssocCommSemiring R]:
- In commutative semirings, left and right multiplication coincide

== HasDistribNeg

=== Opposite Negation

`MulOpposite.instHasDistribNeg`: Distributive negation on opposite
- `neg_mul`: Negation distributes over multiplication from left
- `mul_neg`: Negation distributes over multiplication from right

== Special Results

=== Vieta's Formula

`vieta_formula_quadratic`: For quadratic $x^2 - b x + c = 0$
- If `x` is a root, then exists `y` with:
  - `x + y = b`
  - `x * y = c`

== Implementation Notes

- Uses `@[simps]` for automatic simplification lemma generation
- Coercion lemmas marked with `@[simp, norm_cast]`
- Local simp attributes for specific proofs (e.g., commutativity in Vieta)