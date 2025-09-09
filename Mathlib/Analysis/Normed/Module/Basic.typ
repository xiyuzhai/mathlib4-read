#set document(title: "Normed Spaces and Modules")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Normed Spaces and Modules

== Overview

This module defines normed spaces (vector spaces with compatible norms) and normed algebras over normed fields. The key structure is `NormedSpace`, which combines a module structure with a norm satisfying the fundamental scaling property $‖c dot x‖ = ‖c‖ dot ‖x‖$.

== Main Definition

=== NormedSpace
A normed space over a normed field $𝕜$ is a vector space $E$ with a norm satisfying:
$$‖a dot b‖ ≤ ‖a‖ dot ‖b‖$$

In fact, equality always holds (proved as `norm_smul`), but we only require the inequality in the definition for flexibility.

Key insight: This works for "semi-normed spaces" too, since we only require `SeminormedAddCommGroup` rather than `NormedAddCommGroup`.

== Core Properties

=== Scalar Multiplication and Norms
The fundamental property of normed spaces:
- $‖c dot x‖ = ‖c‖ dot ‖x‖$ (exact equality, though only $≤$ is required)
- $‖n dot x‖ = |n| dot ‖x‖$ for integer scalars $n in ℤ$
- $‖n dot x‖ = n dot ‖x‖$ for natural scalars $n in ℕ$

=== Continuity Properties
Scalar multiplication interacts continuously with limits:
- If $f_n → 0$ and $‖g_n‖$ is bounded, then $f_n dot g_n → 0$
- If $‖f_n‖$ is bounded and $g_n → 0$, then $f_n dot g_n → 0$

These properties are essential for analysis in normed spaces.

== Standard Instances

=== Field as Normed Space
Every normed field $𝕜$ is naturally a normed space over itself:
$$‖a dot b‖ = ‖a b‖ = ‖a‖ dot ‖b‖$$

=== Product Spaces
The product $E × F$ of normed spaces is a normed space with the sup norm:
$$‖(x, y)‖ = max(‖x‖, ‖y‖)$$
$$‖c dot (x, y)‖ = (‖c dot x‖, ‖c dot y‖) = ‖c‖ dot max(‖x‖, ‖y‖)$$

=== Pi Types
For finitely many normed spaces $E_i$, the product $∏_i E_i$ is a normed space:
$$‖f‖ = sup_i ‖f_i‖$$
This generalizes the finite product case.

=== Subspaces
Every submodule of a normed space inherits the normed space structure:
- The norm is simply restricted from the ambient space
- The scaling property is inherited automatically

=== Induced Structures
Given a linear map $f : E → G$ where $G$ is a normed space, we can induce a normed space structure on $E$ via:
$$‖x‖_E = ‖f(x)‖_G$$

== Special Structures

=== Opposite Spaces
The multiplicative opposite $E^"op"$ of a normed space is itself a normed space with the same norm.

=== Separation Quotient
The separation quotient (identifying points at distance 0) preserves the normed space structure.

=== ULift
The universe lift of a normed space retains its normed space structure.

== Nontrivially Normed Spaces

When $𝕜$ is a nontrivially normed field and $E$ is nontrivial:

=== Unboundedness
For any $c in ℝ$, there exists $x in E$ with $‖x‖ > c$.

Proof idea: Take any nonzero $x_0$, then scale by large $r in 𝕜$:
$$‖r dot x_0‖ = ‖r‖ dot ‖x_0‖$$
Since $𝕜$ is unbounded, we can make this arbitrarily large.

=== Noncompactness
Consequences of unboundedness:
- The universal set is not bounded
- The cobounded filter is non-trivial ($"NeBot"$)
- The space is not compact

=== Infinitude
Any nontrivially normed field must be infinite (cannot be finite).

== Discrete Subgroups

=== Integer Multiples
For a normed space over $ℚ$, the additive subgroup $ℤ dot e$ (integer multiples of $e ≠ 0$) has discrete topology.

This is because $‖k dot e‖ = |k| dot ‖e‖$, so distinct integer multiples are separated by at least $‖e‖$.

== Type Class Hierarchy

The instance hierarchy:
```
NormedSpace 𝕜 E
    ↓
NormSMulClass 𝕜 E
    ↓
IsBoundedSMul 𝕜 E
```

Special instances with priorities:
- Priority 100: `NormedSpace.toNormSMulClass`
- Priority 75: `SubmoduleClass.toNormedSpace`

== Applications

Normed spaces are fundamental for:
- *Functional Analysis*: Banach spaces, Hilbert spaces
- *Differential Calculus*: Derivatives in infinite dimensions
- *Operator Theory*: Bounded linear operators
- *Approximation Theory*: Best approximation problems
- *PDEs*: Solution spaces for differential equations

== Design Notes

The definition requires only the inequality $‖a dot b‖ ≤ ‖a‖ dot ‖b‖$ rather than equality, making it easier to verify instances. The equality is then proved as a theorem. This design choice simplifies the construction of normed spaces while maintaining full strength in applications.