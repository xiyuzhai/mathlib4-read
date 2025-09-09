#set document(title: "Normed Groups")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Normed Groups

== Overview

This module defines the fundamental structures for normed groups and seminormed groups in Mathlib. It establishes 10 classes that endow types with norm functions and compatible metric structures, forming the foundation for functional analysis and topology.

== Core Norm Classes

=== Norm
The base class `Norm E` equips a type $E$ with a real-valued norm function $norm : E → ℝ$, denoted $‖x‖$. This is an auxiliary class designed to be extended with more specific properties.

=== NNNorm  
The class `NNNorm E` provides a non-negative real-valued norm $"nnnorm" : E → ℝ^{≥0}$, denoted $‖x‖_+$. This ensures the norm values are always non-negative by construction.

=== ENorm
The class `ENorm E` extends to extended non-negative reals with $"enorm" : E → ℝ^{≥0∞}$, denoted $‖x‖_e$. This allows handling of potentially infinite norms.

== Seminormed Structures

=== SeminormedAddGroup
A seminormed additive group combines:
- An additive group structure $(E, +, 0, -)$
- A norm function $‖·‖ : E → ℝ$
- A pseudometric space structure where $"dist"(x, y) = ‖x - y‖$

The key property is that the distance is translation-invariant and determined entirely by the norm of differences.

=== SeminormedGroup
The multiplicative analogue where:
- Group structure $(E, ·, 1, ^{-1})$
- Norm function $‖·‖ : E → ℝ$
- Distance formula: $"dist"(x, y) = ‖x / y‖$

Key theorems include:
- $‖a^{-1}‖ = ‖a‖$ (norm preservation under inversion)
- $‖a b‖ ≤ ‖a‖ + ‖b‖$ (triangle inequality)

=== SeminormedAddCommGroup & SeminormedCommGroup
These add commutativity to the respective group operations while maintaining the seminorm structure. The commutativity provides additional symmetry properties useful in analysis.

== Normed Structures

=== NormedAddGroup
Strengthens `SeminormedAddGroup` by replacing the pseudometric with a metric space structure. This adds the separation axiom: $‖x‖ = 0 ⟺ x = 0$.

=== NormedGroup
The multiplicative version with metric space structure and the property: $‖x‖ = 0 ⟺ x = 1$.

=== NormedAddCommGroup & NormedCommGroup
Complete the hierarchy by combining normedness with commutativity, providing the richest structure for analysis.

== Extended Seminormed Structures

=== ESeminormedAddMonoid & ESeminormedMonoid
These classes work with extended norms ($ℝ^{≥0∞}$-valued) and require:
- Continuous enorm function
- Monoid structure
- Compatibility: $‖1‖_e = 0$ and $‖x · y‖_e ≤ ‖x‖_e + ‖y‖_e$

=== ENormedAddMonoid & ENormedMonoid
Add the separation property to extended seminorms: $‖x‖_e = 0 ⟺ x = "identity"$.

== Key Properties and Theorems

=== Distance Formulas
- Additive: $"dist"(a, b) = ‖a - b‖$
- Multiplicative: $"dist"(a, b) = ‖a / b‖$
- Alternative: $"dist"(a, b) = ‖b / a‖$

=== Norm Properties
- *Triangle inequality*: $‖x + y‖ ≤ ‖x‖ + ‖y‖$ (additive) or $‖x y‖ ≤ ‖x‖ + ‖y‖$ (multiplicative)
- *Invariance*: $‖-x‖ = ‖x‖$ (additive) or $‖x^{-1}‖ = ‖x‖$ (multiplicative)
- *Zero/Identity*: $‖0‖ = 0$ (additive) or $‖1‖ = 0$ (multiplicative)
- *Homogeneity for integer powers*: $‖x^n‖ = |n| · ‖x‖$ (for appropriate structures)

=== Continuity
All norm functions in these structures are continuous with respect to their induced topologies. The classes `ContinuousENorm` explicitly require this continuity.

== Applications

These structures form the foundation for:
- Banach spaces (complete normed vector spaces)
- Operator norms and bounded linear maps
- Spectral theory
- Harmonic analysis on groups
- Metric geometry

== Design Notes

The hierarchy uses a non-mixin design for performance, meaning `SeminormedGroup` extends `Group` directly rather than being a separate structure. The convention $"dist"(x, y) = ‖x - y‖$ makes distance right-translation invariant, which aligns with the typical left-action conventions in Mathlib.