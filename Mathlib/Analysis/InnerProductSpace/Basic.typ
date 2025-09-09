#set document(title: "Inner Product Spaces")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Inner Product Spaces - Basic Properties

== Overview

This module establishes fundamental properties of inner product spaces over real or complex fields. Inner product spaces generalize the notion of angle and length from Euclidean spaces to arbitrary vector spaces, providing the foundation for Hilbert space theory and functional analysis.

== Core Properties

=== Conjugate Symmetry
The inner product satisfies conjugate symmetry:
$$angle.l y, x angle.r^† = angle.l x, y angle.r$$

For real inner products, this reduces to commutativity:
$$angle.l y, x angle.r_ℝ = angle.l x, y angle.r_ℝ$$

=== Self-Inner Product
For any vector $x$:
- The imaginary part vanishes: $"Im" angle.l x, x angle.r = 0$
- The value is always real and non-negative

== Linearity Properties

=== Additivity
The inner product is additive in both arguments:
- Left additivity: $angle.l x + y, z angle.r = angle.l x, z angle.r + angle.l y, z angle.r$
- Right additivity: $angle.l x, y + z angle.r = angle.l x, y angle.r + angle.l x, z angle.r$

=== Scalar Multiplication
For scalar multiplication by $r in 𝕜$:
- Left: $angle.l r dot x, y angle.r = r^† dot angle.l x, y angle.r$
- Right: $angle.l x, r dot y angle.r = r dot angle.l x, y angle.r$

For real scalars $r in ℝ$:
- Both sides: $angle.l r dot x, y angle.r = angle.l x, r dot y angle.r = r dot angle.l x, y angle.r$

=== General Algebra Actions
For a commutative semiring $𝕝$ acting on the space:
- With star structure: $angle.l r dot x, y angle.r = r^† dot angle.l x, y angle.r$
- Trivial star (e.g., $ℕ, ℤ, ℚ, ℝ$): $angle.l r dot x, y angle.r = r dot angle.l x, y angle.r$

== Symmetry Properties

=== Real and Imaginary Parts
- Real part symmetry: $"Re" angle.l x, y angle.r = "Re" angle.l y, x angle.r$
- Imaginary part antisymmetry: $"Im" angle.l x, y angle.r = -"Im" angle.l y, x angle.r$

=== Zero Inner Product
The condition $angle.l x, y angle.r = 0$ is symmetric:
$$angle.l x, y angle.r = 0 ⟺ angle.l y, x angle.r = 0$$

== Sesquilinear and Bilinear Forms

=== Sesquilinear Form
The inner product defines a sesquilinear form:
$$"sesqFormOfInner" : E →_𝕜 E →_⋆[𝕜] 𝕜$$

This captures the conjugate-linearity in the first argument and linearity in the second.

=== Bilinear Form (Real Case)
For real inner product spaces, we get a bilinear form:
$$"bilinFormOfRealInner" : "BilinForm" space ℝ space F$$

Note the argument order is preserved (unlike the sesquilinear form).

== Summation Formulas

=== Finite Sums
Inner products distribute over finite sums:
- Left sum: $angle.l sum_(i in s) f_i, x angle.r = sum_(i in s) angle.l f_i, x angle.r$
- Right sum: $angle.l x, sum_(i in s) f_i angle.r = sum_(i in s) angle.l x, f_i angle.r$

=== Finsupp Sums
For finitely supported functions $l : ι →_0 𝕜$:
$$angle.l sum_i l_i dot v_i, x angle.r = sum_i "conj"(l_i) dot angle.l v_i, x angle.r$$

== Main Theorems (Referenced)

=== Cauchy-Schwarz Inequality
The fundamental inequality (proved later in the file):
$$|angle.l x, y angle.r|^2 ≤ angle.l x, x angle.r dot angle.l y, y angle.r$$

Equality holds if and only if $x$ and $y$ are linearly dependent.

=== Polarization Identity
Expresses inner product in terms of norms:
$$angle.l x, y angle.r = frac(‖x + y‖^2 - ‖x - y‖^2 + i(‖x + i y‖^2 - ‖x - i y‖^2), 4)$$

For real spaces:
$$angle.l x, y angle.r_ℝ = frac(‖x + y‖^2 - ‖x - y‖^2, 4)$$

== Applications

These properties are fundamental for:
- *Hilbert space theory*: Complete inner product spaces
- *Orthogonality*: Perpendicular vectors and projections
- *Spectral theory*: Self-adjoint operators and eigenvalues
- *Quantum mechanics*: State spaces and observables
- *Signal processing*: Fourier analysis and filtering

== Design Notes

The module uses `RCLike` to handle both real and complex cases uniformly. The notation $angle.l x, y angle.r$ represents the inner product, with subscript $ℝ$ for explicitly real inner products. The conjugate operation is denoted by $†$ (dagger).

The sesquilinear form approach provides a clean categorical perspective on inner products, facilitating the development of abstract theory while maintaining computational convenience.