#set document(title: "Complex Numbers as a Normed Field")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Complex Numbers as a Normed Field

== Overview

This module establishes $ℂ$ as a normed field and explores its analytical properties. It provides the fundamental continuous linear maps between $ℂ$ and $ℝ$, establishing the real vector space structure of $ℂ$ with proper topological properties.

== Core Structure

=== Normed Field Instance
The complex numbers form a normed field where:
- The norm is the standard modulus: $‖z‖ = sqrt(x^2 + y^2)$ for $z = x + i y$
- Distance is induced by the norm: $d(z, w) = ‖z - w‖$
- Multiplicative property: $‖z w‖ = ‖z‖ dot ‖w‖$

=== Densely Normed Field
$ℂ$ is densely normed: for any $0 < r_1 < r_2$, there exists $z in ℂ$ with $r_1 < ‖z‖ < r_2$.

This is achieved by taking real numbers between $r_1$ and $r_2$.

== Continuous Linear Maps

The module defines several fundamental continuous linear maps treating $ℂ$ as a real vector space:

=== Real and Imaginary Parts
|Function|Type|Description|
|--------|----------|-----------|
|`reCLM`|$ℂ →_L^ℝ ℝ$|Real part as continuous linear map|
|`imCLM`|$ℂ →_L^ℝ ℝ$|Imaginary part as continuous linear map|

Properties:
- Both are 1-Lipschitz: $|"Re"(z)| ≤ ‖z‖$ and $|"Im"(z)| ≤ ‖z‖$
- Both are uniformly continuous
- Together they decompose any complex number

=== Complex Embedding of Reals
|Function|Type|Description|
|--------|----------|-----------|
|`ofRealCLM`|$ℝ →_L^ℝ ℂ$|Embedding of reals|
|`ofRealLI`|$ℝ →_(l i)^ℝ ℂ$|Embedding as linear isometry|

The embedding preserves norms: $‖(r : ℂ)‖ = |r|$ for $r in ℝ$.

=== Complex Conjugation
|Function|Type|Description|
|--------|----------|-----------|
|`conjCLE`|$ℂ ≃_L^ℝ ℂ$|Conjugation as continuous linear equiv|
|`conjLIE`|$ℂ ≃_(l i)^ℝ ℂ$|Conjugation as linear isometry equiv|

Conjugation is an isometry: $‖overline(z)‖ = ‖z‖$.

== The Real Product Equivalence

=== Main Equivalence
The natural identification $ℂ ≃ ℝ × ℝ$ is formalized as:
"equivRealProdCLM" : ℂ ≃ ℝ × ℝ (as continuous linear equivalence)

This maps $z = x + i y$ to $(x, y)$ and is:
- 1-Lipschitz in the forward direction
- $(sqrt(2))^(-1)$-antilipschitz
- A uniform embedding

=== Norm Relationships
For $z in ℂ$ and its image $(x, y) in ℝ × ℝ$:
- $‖(x, y)‖ ≤ ‖z‖$ (using sup norm on product)
- $‖z‖ ≤ sqrt(2) dot max(|x|, |y|)$

This establishes that the two norm structures are equivalent.

== Topological Properties

=== Completeness
$ℂ$ is a complete metric space. This follows from:
1. $ℝ × ℝ$ is complete (product of complete spaces)
2. The equivalence `equivRealProdCLM` is a uniform embedding
3. Completeness is preserved by uniform embeddings

=== Properness
$ℂ$ is a proper space (closed bounded sets are compact):
- The norm function $‖·‖ : ℂ → ℝ$ is proper
- The norm-squared function is also proper
- This makes $ℂ$ locally compact

=== Hausdorff Property
$ℂ$ is a $T_2$ (Hausdorff) space, as every metric space is Hausdorff.

== Normed Algebra Structure

=== Over Any Normed Field
For any normed field $R$ with a normed algebra structure over $ℝ$, we get a normed algebra structure of $R$ over $ℂ$:
$$‖r dot z‖ ≤ ‖r‖ dot ‖z‖$$

=== Complex-to-Real Restriction
Any $ℂ$-normed space $E$ is automatically an $ℝ$-normed space by scalar restriction. This is formalized with appropriate instance priorities to avoid diamond problems.

== Special Properties

=== Roots of Unity
If $ζ^n = 1$ for some $n ≠ 0$, then $‖ζ‖ = 1$.

Proof: $‖ζ‖^n = ‖ζ^n‖ = ‖1‖ = 1$, so $‖ζ‖ = 1$.

=== Norm-Squared Function
The function $"normSq"(z) = ‖z‖^2 = |z|^2$ is:
- Continuous
- Proper (preimages of bounded sets are bounded)
- Tends to infinity along the cocompact filter

=== Integer Casts
For $n in ℤ$: $‖(n : ℂ)‖ = |n|$

This cannot be proved earlier because it requires the normed ring structure on $ℤ$.

== RCLike Instance

$ℂ$ is registered as an `RCLike` field, meaning it satisfies the axioms for fields that behave like $ℝ$ or $ℂ$:
- Complete normed field
- Nontrivial
- Has a conjugation operation
- Satisfies the identity $‖z‖^2 = z dot overline(z)$

== Applications

This structure is fundamental for:
- *Complex Analysis*: Holomorphic functions, Cauchy theory
- *Fourier Analysis*: Complex exponentials and Fourier transforms
- *Operator Theory*: Spectrum of operators, functional calculus
- *Quantum Mechanics*: Complex Hilbert spaces

== Design Notes

The module carefully manages instance priorities to ensure that the complex-to-real scalar restriction works smoothly without creating diamond problems in the typeclass hierarchy. The use of continuous linear maps rather than bare functions ensures that all operations respect the topological structure.