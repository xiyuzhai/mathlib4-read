#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Fiber.lean* file in Mathlib4. The file develops the theory of scheme-theoretic fibers, which are fundamental objects in algebraic geometry that capture the "local structure" of morphisms at individual points. Fibers provide crucial information about the geometric and arithmetic properties of morphisms.

= Basic Definitions

== The Scheme-Theoretic Fiber

```lean
def Scheme.Hom.fiber (f : X.Hom Y) (y : Y) : Scheme := pullback f (Y.fromSpecResidueField y)
```

*Natural Language:* The fiber of a morphism $f: X \to Y$ at a point $y \in Y$ is defined as the pullback (fibered product) of $f$ with the canonical morphism $\mathrm{Spec}(\kappa(y)) \to Y$, where $\kappa(y)$ is the residue field at $y$.

This captures the intuitive idea that the fiber consists of all points in $X$ that map to $y$, together with their "infinitesimal neighborhoods" encoded by the residue field structure.

== Fiber Inclusion

```lean
def Scheme.Hom.fiber$\iota$ (f : X.Hom Y) (y : Y) : f.fiber y -> X := pullback.fst _ _
```

*Natural Language:* The fiber inclusion $f.fiber\iota\, y: f.fiber\, y \to X$ embeds the fiber as a subscheme of $X$. This morphism allows us to view the fiber as sitting naturally inside the domain of $f$.

== Fiber to Residue Field

```lean
def Scheme.Hom.fiberToSpecResidueField (f : X.Hom Y) (y : Y) :
    f.fiber y -> Spec (Y.residueField y) :=
  pullback.snd _ _
```

*Natural Language:* There is a canonical morphism from the fiber to $\mathrm{Spec}(\kappa(y))$, making the fiber naturally a $\kappa(y)$-scheme. This captures the algebraic structure of the fiber over the residue field.

= Topological Properties

== Range Characterization

```lean
lemma Scheme.Hom.range_fiber$\iota$ (f : X.Hom Y) (y : Y) :
    Set.range (f.fiber$\iota$ y).base = f.base ^(-1)' {y}
```

*Natural Language:* The underlying topological space of the fiber $f.fiber\, y$ corresponds exactly to the set-theoretic fiber $f^{-1}(\{y\}) \subseteq X$. This shows that the scheme-theoretic fiber has the correct underlying point set.

== Homeomorphism with Set-Theoretic Fiber

```lean
def Scheme.Hom.fiberHomeo (f : X.Hom Y) (y : Y) : f.fiber y ~_t f.base ^(-1)' {y}
```

*Natural Language:* The scheme-theoretic fiber is homeomorphic to the set-theoretic fiber $f^{-1}(\{y\})$ as topological spaces. This establishes that the scheme structure on the fiber is compatible with the natural topology.

== Points as Fiber Elements

```lean
def Scheme.Hom.asFiber (f : X.Hom Y) (x : X) : f.fiber (f.base x) :=
    (f.fiberHomeo (f.base x)).symm <x, rfl>
```

*Natural Language:* Any point $x \in X$ can be viewed as a point in the fiber of $f$ over $f(x)$. This gives a canonical way to think of points of $X$ as living in the appropriate fibers.

= Morphism Properties

== Preimmersion Property

```lean
instance (f : X -> Y) (y : Y) : IsPreimmersion (f.fiber$\iota$ y)
```

*Natural Language:* The fiber inclusion is always a preimmersion, meaning it is locally of finite type and has geometrically reduced fibers. This is a fundamental property that ensures fibers have good geometric behavior.

= Preservation of Properties

== Quasi-Compactness

```lean
instance (f : X -> Y) [QuasiCompact f] (y : Y) : CompactSpace (f.fiber y)
```

*Natural Language:* If $f$ is quasi-compact, then each fiber is a compact topological space. This is a key result showing that quasi-compactness is preserved when passing to fibers.

```lean
lemma QuasiCompact.isCompact_preimage_singleton (f : X -> Y) [QuasiCompact f] (y : Y) :
    IsCompact (f.base ^(-1)' {y})
```

*Natural Language:* For quasi-compact morphisms, the set-theoretic fiber $f^{-1}(\{y\})$ is compact as a subspace of $X$. This provides the topological foundation for the compactness of scheme-theoretic fibers.

== Affine Property

```lean
instance (f : X -> Y) [IsAffineHom f] (y : Y) : IsAffine (f.fiber y)
```

*Natural Language:* If $f$ is an affine morphism, then each fiber is an affine scheme. This shows that the affine property descends to fibers, which is crucial for many constructions in algebraic geometry.

== Jacobson Property

```lean
instance (f : X -> Y) (y : Y) [LocallyOfFiniteType f] : JacobsonSpace (f.fiber y)
```

*Natural Language:* Fibers of locally finite type morphisms are Jacobson spaces, meaning that every prime ideal is an intersection of maximal ideals. This is important for understanding the arithmetic properties of fibers.

= Finite Morphisms and Discrete Fibers

== Finiteness of Fibers

```lean
instance (f : X -> Y) (y : Y) [IsFinite f] : Finite (f.fiber y)
```

*Natural Language:* If $f$ is a finite morphism, then each fiber has only finitely many points. This is a fundamental property of finite morphisms that makes them algebraically tractable.

== Finite Preimages

```lean
lemma IsFinite.finite_preimage_singleton (f : X -> Y) [IsFinite f] (y : Y) :
    (f.base ^(-1)' {y}).Finite
```

*Natural Language:* For finite morphisms, the set-theoretic fiber over any point is a finite set. This provides the topological foundation for the finiteness of scheme-theoretic fibers.

== General Finite Preimages

```lean
lemma Scheme.Hom.finite_preimage (f : X.Hom Y) [IsFinite f] {s : Set Y} (hs : s.Finite) :
    (f.base ^(-1)' s).Finite
```

*Natural Language:* Finite morphisms have the property that preimages of finite sets are finite. This extends the finiteness property from individual points to arbitrary finite subsets of the codomain.

== Discrete Topology

```lean
instance Scheme.Hom.discrete_fiber (f : X -> Y) (y : Y) [IsFinite f] :
    DiscreteTopology (f.fiber y)
```

*Natural Language:* Fibers of finite morphisms carry the discrete topology. Since they are both finite and compact (being fibers of quasi-compact morphisms), they must be discrete.

= Residue Field Structure

== Canonical Over-Structure

```lean
instance (f : X.Hom Y) (y : Y) : (f.fiber y).CanonicallyOver X where hom := f.fiber$\iota$ y
```

*Natural Language:* The fiber naturally has the structure of an $X$-scheme via the fiber inclusion. This allows us to study the fiber in relation to the original domain scheme.

== Residue Field Scheme Structure

```lean
@[reducible] def Scheme.Hom.fiberOverSpecResidueField
    (f : X.Hom Y) (y : Y) : (f.fiber y).Over (Spec (Y.residueField y))
```

*Natural Language:* The fiber also has the structure of a scheme over $\mathrm{Spec}(\kappa(y))$, where $\kappa(y)$ is the residue field at $y$. This captures the algebraic relationship between the fiber and the base point.

== Closed Point Property

```lean
lemma Scheme.Hom.fiberToSpecResidueField_apply (f : X.Hom Y) (y : Y) (x : f.fiber y) :
    (f.fiberToSpecResidueField y).base x = IsLocalRing.closedPoint (Y.residueField y)
```

*Natural Language:* Under the morphism to $\mathrm{Spec}(\kappa(y))$, every point of the fiber maps to the unique closed point. This reflects the fact that $\kappa(y)$ is a field, so its spectrum has only one point.

= Geometric Interpretation

== Local Structure

The scheme-theoretic fiber captures several important aspects:
\item *Point-wise behavior*: Which points in $X$ map to a given point $y \in Y$
\item *Infinitesimal structure*: How the morphism behaves in neighborhoods of these points
\item *Algebraic structure*: The relationship between local rings and the residue field
\item *Geometric multiplicities*: Information about ramification and branching

== Applications

Scheme-theoretic fibers are crucial for:
\item *Flatness*: A morphism is flat if and only if all fibers are flat over the residue fields
\item *Smoothness*: Smooth morphisms have smooth fibers
\item *Proper morphisms*: Studying compactification and properness via fiber behavior
\item *Dimension theory*: The dimension of fibers relates to the relative dimension

= Examples and Special Cases

== Affine Morphisms

For affine morphisms $f: X = \mathrm{Spec*(A) \to Y = \mathrm{Spec}(B)$ corresponding to a ring homomorphism $\phi: B \to A$:
\item The fiber over a point $y$ corresponding to prime $\mathfrak{p* \subset B$ is $\mathrm{Spec}(A \otimes_B \kappa(\mathfrak{p}))$
\item This connects to the tensor product construction in commutative algebra

== Finite Morphisms

For finite morphisms:
\item Each fiber is a finite scheme (finitely many points)
\item The points correspond to primes lying over the base prime
\item Multiplicities are encoded in the scheme structure

== Smooth Morphisms

For smooth morphisms:
\item All fibers are smooth schemes
\item The dimension of fibers is constant (relative dimension)
\item Local structure is particularly well-behaved

= Relationship to Classical Theory

== Algebraic Number Theory

In arithmetic geometry, fibers are closely related to:
\item *Primes lying over*: Points in fibers correspond to primes lying over a given prime
\item *Ramification*: The scheme structure encodes ramification information
\item *Decomposition groups*: The fiber structure relates to Galois-theoretic decomposition

== Complex Algebraic Geometry

In the complex setting:
\item Fibers over $\mathbb{C*$-points are complex varieties
\item The topological structure relates to the analytic topology
\item Proper morphisms give compact fibers

= Conclusion

The `Fiber.lean* file provides:

== Foundational Definitions

\item Rigorous definition of scheme-theoretic fibers
\item Connection to pullback constructions and residue fields
\item Proper embedding of fibers into domain schemes
\item Natural $\kappa(y)$-scheme structure

== Key Properties

\item Topological characterization via set-theoretic fibers
\item Preservation of important morphism properties
\item Finiteness and discreteness results for finite morphisms
\item Compactness results for quasi-compact morphisms

== Geometric Applications

\item Tools for studying local properties of morphisms
\item Foundation for flatness, smoothness, and properness
\item Connection to classical algebraic and arithmetic geometry
\item Framework for dimension theory and multiplicity

== Theoretical Significance

\item Bridges abstract scheme theory with concrete geometric intuition
\item Provides computational tools for studying morphism properties
\item Establishes the connection between global and local behavior
\item Enables systematic study of families and moduli

The theory of scheme-theoretic fibers is fundamental to modern algebraic geometry, providing both conceptual clarity and practical tools for understanding the local and global structure of morphisms between schemes. This formalization in Mathlib4 makes these powerful techniques available for rigorous mathematical reasoning and computation.
