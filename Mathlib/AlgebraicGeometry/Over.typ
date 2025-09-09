#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Over.lean* file in Mathlib4. The file defines typeclasses for working with schemes and morphisms "over" a base scheme $S$. This is fundamental in relative algebraic geometry, where we study families of schemes parametrized by a base scheme and morphisms that are compatible with this parametrization.

= The Over Structure

== Base Scheme Structure

```lean
protected abbrev Over (X S : Scheme.{u}) := OverClass X S
```

*Natural Language:* The typeclass `X.Over S} provides the data of a structure morphism $X \searrow S : X \to S$, making $X$ an $S$-scheme. This captures the fundamental concept of relative algebraic geometry where schemes are studied in relation to a fixed base scheme.

In classical algebraic geometry, this corresponds to:
\item Varieties over a field $k$ (where $S = \mathrm{Spec*(k)$)
\item Schemes over $\mathbb{Z*$ (arithmetic geometry)
\item Families of schemes parametrized by a base scheme
\item Relative constructions like relative Spec and relative Proj

== Canonical Over Structure

```lean
abbrev CanonicallyOver (X S : Scheme.{u}) := CanonicallyOverClass X S
```

*Natural Language:* The typeclass `X.CanonicallyOver S} indicates that $X$ has a canonical structure as an $S$-scheme, where the base scheme $S$ can be uniquely inferred from the structure of $X$. This is used when there is a "natural" or "canonical" choice of base scheme.

Examples include:
\item Open subschemes of $X$ are canonically over $X$
\item Fiber products $X \times_S Y$ are canonically over $S$
\item Scheme-theoretic fibers are canonically over the base point

= Morphisms Over a Base

== Over Morphism Typeclass

```lean
abbrev Hom.IsOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] := HomIsOver f S
```

*Natural Language:* Given schemes $X$ and $Y$ that are both over $S$, a morphism $f: X \to Y$ has type `f.IsOver S} if it commutes with the structure morphisms to $S$. This means the following diagram commutes:
\[
X \arrow[r, "f"] \arrow[dr, "X \searrow S"'] & Y \arrow[d, "Y \searrow S"]
& S
\]

== Characterization of Over Morphisms

```lean
@[simp]
lemma Hom.isOver_iff [X.Over S] [Y.Over S] {f : X ⟶ Y} : f.IsOver S ↔ f ≫ Y ↘ S = X ↘ S
```

*Natural Language:* A morphism $f: X \to Y$ is an $S$-morphism if and only if composing $f$ with the structure morphism $Y \to S$ gives the same result as the structure morphism $X \to S$.

This is the fundamental compatibility condition that makes $f$ a morphism of $S$-schemes rather than just a morphism of schemes.

= Bundled Objects and Morphisms

== Bundled Over Objects

```lean
abbrev asOver (X S : Scheme.{u}) [X.Over S] := OverClass.asOver X S
```

*Natural Language:* Given an $S$-scheme $X$, we can form the bundled object `X.asOver S} which packages both the scheme $X$ and its structure morphism to $S$ into a single object in the category of schemes over $S$.

== Bundled Over Morphisms

```lean
abbrev Hom.asOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] [f.IsOver S] :=
  OverClass.asOverHom S f
```

*Natural Language:* Given an $S$-morphism $f: X \to Y$, we can form the bundled morphism `f.asOver S} in the category of schemes over $S$.

= Categorical Structure

== The Over Category

The bundled objects and morphisms naturally organize into the **over category** $\mathbf{Scheme*/S$:
\item *Objects*: Schemes $X$ equipped with morphisms $X \to S$
\item *Morphisms*: Morphisms $f: X \to Y$ that make the triangle commute
\item *Composition*: Ordinary composition of scheme morphisms
\item *Identity*: Identity morphisms (which automatically commute with structure morphisms)

== Functorial Properties

Over categories satisfy many important properties:
\item They have pullbacks (fibered products over $S$)
\item They have terminal objects ($S$ itself)
\item They inherit many limits and colimits from the base category
\item Base change functors between over categories are well-behaved

= Examples and Applications

== Varieties over a Field

When $S = \mathrm{Spec*(k)$ for a field $k$:
\item $X.Over\, S$ means $X$ is a $k$-variety
\item Morphisms over $S$ are $k$-morphisms
\item This is the classical setting of algebraic geometry over fields

== Arithmetic Geometry

When $S = \mathrm{Spec*(\mathbb{Z})$:
\item $X.Over\, S$ means $X$ is defined over the integers
\item This is the setting for studying arithmetic properties of schemes
\item Base change to $\mathrm{Spec*(\mathbb{F}_p)$ gives reduction modulo $p$

== Families of Schemes

For a general base scheme $S$:
\item Objects over $S$ represent families of schemes parametrized by $S$
\item Points $s \in S$ correspond to fibers of the family
\item Morphisms over $S$ are morphisms of families that preserve the parametrization

== Relative Constructions

Many constructions in algebraic geometry are naturally relative:
\item *Relative Spec*: $\mathrm{Spec}_S(\mathcal{A})$ for a quasi-coherent $\mathcal{O}_S$-algebra $\mathcal{A}$
\item *Relative Proj*: $\mathrm{Proj}_S(\mathcal{A})$ for a graded $\mathcal{O}_S$-algebra $\mathcal{A}$
\item *Fiber products*: $X \times_S Y$ for schemes $X, Y$ over $S$
\item *Base change*: Pulling back families along morphisms $T \to S$

= Over Towers and Transitivity

== Tower Structure

The file references the existence of `CategoryTheory.IsOverTower X Y S*, which handles the situation where we have a tower of base schemes:
\[
X \to Y \to S
\]

This allows for more complex relative situations where schemes are parametrized over intermediate bases.

== Composition of Over Structures

If $X$ is over $Y$ and $Y$ is over $S$, then $X$ is naturally over $S$ via composition. The typeclass system can handle this automatically through appropriate instances.

= Technical Implementation

== Thin Wrapper Design

The file implements over structures as "thin wrappers" around the more general `CategoryTheory/Comma/OverClass* framework. This provides:
\item Consistency with the general category theory library
\item Reuse of existing infrastructure for over categories
\item Specialized terminology and notation for scheme theory
\item Integration with scheme-specific constructions

== Typeclass Inference

The typeclass system allows for automatic inference of over structures:
\item When the base scheme is clear from context, it can be inferred
\item Morphisms automatically inherit over properties when appropriate
\item Complex over structures can be built compositionally

= Relationship to Classical Theory

== Grothendieck's Relative Point of View

This formalization embodies Grothendieck's revolutionary insight that many constructions in algebraic geometry are best understood in a relative setting:
\item Properties of schemes are often relative to a base
\item Families of schemes are fundamental objects of study
\item Base change and specialization provide powerful tools
\item Descent theory works in the relative setting

== Moduli Theory

Over structures are essential for moduli theory:
\item Moduli spaces parametrize families of geometric objects
\item Universal properties are naturally expressed in over categories
\item Deformation theory studies families over infinitesimal bases
\item Algebraic stacks generalize the notion of moduli spaces

= Integration with Other Mathlib Components

== Pullbacks and Base Change

The over structure integrates naturally with:
\item Pullback constructions (fibered products)
\item Base change functors
\item Flat morphisms and faithfully flat descent
\item Proper and smooth morphisms

== Cohomology and Descent

Over structures provide the foundation for:
\item Sheaf cohomology in the relative setting
\item Descent theory for morphisms and objects
\item Faithfully flat topology and étale cohomology
\item Higher category theory and derived categories

= Conclusion

The `Over.lean* file provides:

== Foundational Infrastructure

\item Clean typeclass-based interface for relative algebraic geometry
\item Integration with general category theory frameworks
\item Automatic inference and composition of over structures
\item Bundling facilities for working with over categories

== Conceptual Framework

\item Formalization of Grothendieck's relative point of view
\item Foundation for families and moduli theory
\item Support for base change and specialization
\item Framework for relative constructions

== Technical Benefits

\item Type safety for ensuring morphisms respect base structures
\item Automatic propagation of over properties
\item Clean notation and terminology for scheme theory
\item Extensibility for more complex relative situations

== Mathematical Applications

\item Essential for studying families of algebraic varieties
\item Foundation for arithmetic geometry and number theory
\item Key component for moduli spaces and parameter spaces
\item Support for advanced topics like stacks and derived geometry

This typeclass-based approach to relative algebraic geometry provides both conceptual clarity and practical tools for working with schemes in relation to base schemes. It embodies modern perspectives on algebraic geometry while providing concrete computational tools for mathematical reasoning and proof development.
