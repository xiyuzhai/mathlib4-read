#set document(title: "Locally Convex Spaces - Basic Concepts")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Locally Convex Spaces - Basic Concepts

== Overview

This module introduces the fundamental concepts for locally convex topological vector spaces (LCTVS): absorbent and balanced sets. These are the building blocks for understanding neighborhoods of the origin in topological vector spaces, generalizing the notion of balls in normed spaces.

== Core Definitions

=== Balanced Sets
A set $A subset.eq E$ is *balanced* with respect to $𝕜$ if:
$$a dot A subset.eq A text(" whenever ") ‖a‖ ≤ 1$$

Intuitively, a balanced set "surrounds the origin uniformly" - it contains all scalings by coefficients of norm at most 1.

Equivalent characterizations:
- $"Balanced" space 𝕜 space A ⟺ ∀ a in 𝕜, ‖a‖ ≤ 1 ⟹ a dot A subset.eq A$
- $"Balanced" space 𝕜 space A ⟺ "closedBall"(0, 1) dot A subset.eq A$
- For elements: $x in A ⟹ a dot x in A$ whenever $‖a‖ ≤ 1$

=== Absorbing Sets
A set $A$ *absorbs* a set $B$ if $B$ is contained in all sufficiently large scalings of $A$:
$$"Absorbs" space 𝕜 space A space B ⟺ ∃ r > 0, ∀ c in 𝕜, ‖c‖ ≥ r ⟹ B subset.eq c dot A$$

This captures the idea that $A$ eventually "swallows" $B$ under scaling.

=== Absorbent Sets
A set $A$ is *absorbent* if it absorbs every singleton (equivalently, every point):
$$"Absorbent" space 𝕜 space A ⟺ ∀ x in E, "Absorbs" space 𝕜 space A space {x}$$

Absorbent sets are the vector space analogue of neighborhoods of the origin.

== Properties of Balanced Sets

=== Closure Under Operations

Balanced sets are preserved by:
- **Union**: If $A$ and $B$ are balanced, so is $A union B$
- **Intersection**: If $A$ and $B$ are balanced, so is $A sect B$
- **Arbitrary unions**: $union_i A_i$ is balanced if all $A_i$ are balanced
- **Arbitrary intersections**: $sect_i A_i$ is balanced if all $A_i$ are balanced

=== Module Operations

For balanced sets in modules:
- **Negation**: $A$ balanced $⟺$ $-A$ balanced
- **Addition**: $A, B$ balanced $⟹$ $A + B$ balanced
- **Subtraction**: $A, B$ balanced $⟹$ $A - B$ balanced
- **Scalar multiplication**: If $A$ is balanced and scalars commute, then $a dot A$ is balanced

=== Special Cases

- The empty set $∅$ is balanced
- The universal set is balanced
- The zero set ${0}$ is balanced

=== Symmetry Property

In normed spaces with $‖-1‖ = 1$:
- Balanced sets are symmetric: $x in A ⟺ -x in A$
- Therefore: $-A = A$ for balanced sets

== Properties of Absorbing Sets

=== Neighborhood Characterization

For normed division rings:
$$"Absorbs" space 𝕜 space A space B ⟺ ∀^F c in cal(N)[≠] 0, c dot B subset.eq A$$

where $cal(N)[≠] 0$ is the punctured neighborhood of 0.

If $0 in A$, this simplifies to:
$$"Absorbs" space 𝕜 space A space B ⟺ ∀^F c in cal(N) space 0, c dot B subset.eq A$$

=== Monotonicity

For balanced sets, scalar multiplication is monotone:
$$"Balanced" space A ∧ ‖a‖ ≤ ‖b‖ ⟹ a dot A subset.eq b dot A$$

This shows that balanced sets expand monotonically with the norm of the scalar.

== Preimages and Morphisms

=== Preimage Property

If $f : E →[𝕜] F$ is a $𝕜$-linear map and $S subset.eq F$ is balanced, then:
$$f^(-1)(S) text(" is balanced in ") E$$

This is crucial for showing that balanced neighborhoods pull back under continuous linear maps.

== Relationship to Convexity

While this module focuses on balanced and absorbent sets, these concepts are intimately connected to convexity:

- In real vector spaces, balanced convex sets are exactly the symmetric convex sets
- The intersection of all balanced convex neighborhoods of 0 gives the finest locally convex topology
- Absorbent balanced convex sets are exactly the neighborhoods of 0 in locally convex spaces

== Applications

These concepts are fundamental for:

=== Locally Convex Topology
- Defining the finest locally convex topology
- Characterizing continuous seminorms
- Hahn-Banach theorem in locally convex spaces

=== Functional Analysis
- Polar sets and bipolar theorem
- Weak and weak-star topologies
- Barrel and bornological spaces

=== Optimization
- Constraint qualifications in infinite dimensions
- Subdifferential calculus
- Variational analysis

== Design Notes

The module uses filter-based definitions for absorption, allowing seamless integration with Mathlib's topology library. The use of `NormSMulClass` provides flexibility in the types of scalar multiplication considered.

The deprecated aliases for `nhdsWithin` reflect a recent refactoring to use the cleaner `𝓝[≠] 0` notation for punctured neighborhoods.