#set document(title: "Convex Sets")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Convex Sets

== Overview

This module establishes the fundamental theory of convex sets in vector spaces over ordered semirings. A set is convex if it contains all line segments between any two of its points. This concept is central to optimization, functional analysis, and geometric analysis.

== Main Definition

=== Convex
A set $s$ in a $k$-vector space $E$ is *convex* if for any two points $x, y in s$ and any coefficients $a, b in k$ with $a >= 0$, $b >= 0$, and $a + b = 1$, the point $a dot x + b dot y$ is also in $s$.

Formally: `Convex 𝕜 s := ∀ x ∈ s, StarConvex 𝕜 x s`

This definition states that $s$ is convex if and only if it is star-convex with respect to every point in $s$.

== Equivalent Characterizations

=== Segment Inclusion
A set $s$ is convex if and only if for any two points $x, y in s$, the entire segment $[x, y]_k$ is contained in $s$:
$$"Convex" k s ⟺ ∀ x in s, ∀ y in s, bracket.l x, y bracket.r_k subset.eq s$$

=== Open Segment Inclusion
For modules over ordered fields, a set is convex if and only if it contains all open segments between its points:
$$"Convex" k s ⟺ ∀ x in s, ∀ y in s, "openSegment" k space x y subset.eq s$$

=== Pointwise Characterization
A set is convex if and only if for all valid convex combinations:
$$"Convex" k s ⟺ ∀ a, b >= 0, a + b = 1 ⟹ a dot s + b dot s subset.eq s$$

This shows convexity in terms of pointwise set operations.

=== Positive Coefficients
In modules, we can restrict to strictly positive coefficients:
$$"Convex" k s ⟺ ∀ x, y in s, ∀ a, b > 0, a + b = 1 ⟹ a dot x + b dot y in s$$

== Basic Examples

=== Empty Set and Universe
- The empty set $∅$ is convex (vacuously true)
- The universal set is convex

=== Singleton and Subsingleton Sets
Any set with at most one element is convex, as there are no distinct pairs of points to consider.

== Operations Preserving Convexity

=== Intersection
The intersection of convex sets is convex:
- If $s$ and $t$ are convex, then $s ∩ t$ is convex
- More generally, arbitrary intersections preserve convexity: $⋂_i s_i$ is convex if all $s_i$ are convex

=== Products
The Cartesian product of convex sets is convex:
- If $s ⊆ E$ and $t ⊆ F$ are convex, then $s × t$ is convex in $E × F$

=== Pi Types
For dependent functions, if each fiber is convex, the pi-type is convex:
- If $t_i$ is convex for each $i in s$, then $∏_{i in s} t_i$ is convex

=== Directed Unions
A directed union of convex sets is convex:
- If $(s_i)$ is a directed family of convex sets (under inclusion), then $⋃_i s_i$ is convex
- This is crucial for extending local convexity to global convexity

== Relationship with Star Convexity

=== From Convex to Star-Convex
Every convex set is star-convex with respect to each of its points:
- If $s$ is convex and $x in s$, then $s$ is star-convex with respect to $x$

=== Star-Convex Characterization
A nonempty set is convex if and only if it is star-convex with respect to all of its points:
- $s$ convex $⟺$ $∀ x in s$, $s$ is star-convex w.r.t. $x$

== Advanced Properties

=== Pairwise Formulation
Convexity can be characterized through pairwise conditions:
A set $s$ is convex if and only if for any distinct points $x, y in s$ and positive weights summing to 1, their weighted average is in $s$.

=== Convex Combinations
By induction, a convex set contains all finite convex combinations of its points:
- If $x_1, ..., x_n in s$ and $∑_i a_i = 1$ with all $a_i >= 0$, then $∑_i a_i x_i in s$

== Applications

Convex sets appear throughout mathematics:
- *Optimization*: Convex feasible regions ensure local optima are global
- *Functional Analysis*: Convex neighborhoods define locally convex topologies
- *Geometry*: Convex hulls provide minimal convex containers
- *Probability*: Convex sets of distributions have nice mixing properties

== Design Notes

The module uses a star-convex based definition of convexity, which elegantly captures the essence of convexity while facilitating proofs. The hierarchy is designed to work over general ordered semirings, not just real vector spaces, providing maximum generality.