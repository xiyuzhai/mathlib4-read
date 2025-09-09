#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `ResidueField.lean* file in Mathlib4. The file develops the theory of residue fields for points on schemes, which is fundamental to understanding the local behavior of schemes at individual points. The residue field captures the "infinitesimal" or "tangent" information at a point and is essential for studying geometric properties like smoothness, dimension, and rational points.

In classical algebraic geometry, the residue field of a point on an affine variety corresponds to the quotient of the coordinate ring by the maximal ideal defining that point. In scheme theory, this generalizes to the residue field of the local ring (stalk) at any point, providing a universal field that encodes the local geometric behavior.

The residue field is particularly important for understanding:
\item The local nature of geometric properties
\item Rational points and their behavior
\item Morphisms between schemes at the level of individual points
\item The relationship between algebraic and geometric properties

= Basic Definitions

== Residue Field

```lean
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)
```

*Mathematical Significance:* The residue field $\kappa(x)$ of a point $x$ in a scheme $X$ is defined as the residue field of the local ring $\mathcal{O}_{X,x}$ (the stalk at $x$). Since stalks are always local rings, they have a unique maximal ideal, and the residue field is the quotient by this maximal ideal.

Geometrically, the residue field captures the "infinitesimal neighborhood" of the point $x$. It encodes information about how the scheme looks at an infinitesimally small level around that point.

== Field Structure

```lean
instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (IsLocalRing.ResidueField (X.presheaf.stalk x))
```

*Mathematical Significance:* The residue field is indeed a field, which follows from the general theory of local rings. This field structure is crucial for many applications and ensures that residue fields behave like classical fields for geometric purposes.

== Canonical Residue Map

```lean
def residue (X : Scheme.{u}) (x) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))
```

*Mathematical Significance:* The residue map is the canonical surjective ring homomorphism from the stalk $\mathcal{O}_{X,x}$ to the residue field $\kappa(x)$. This map sends elements to their equivalence classes modulo the maximal ideal, effectively "evaluating" them at the point $x$.

The residue map is always surjective and captures the process of "taking values at a point" for regular functions.

= Evaluation Maps

== Evaluation at Points

```lean
def evaluation (U : X.Opens) (x : X) (hx : x ∈ U) : Γ(X, U) ⟶ X.residueField x :=
  X.presheaf.germ U x hx ≫ X.residue _
```

*Mathematical Significance:* For any open subset $U$ containing a point $x$, we have a canonical evaluation map from sections over $U$ to the residue field at $x$. This map represents the geometric process of "evaluating a function at a point."

The evaluation map is the composition of two natural processes:
\item Taking the germ: $\Gamma(X, U) \to \mathcal{O*_{X,x}$
\item Taking the residue: $\mathcal{O*_{X,x} \to \kappa(x)$

== Relationship with Basic Opens

```lean
@[simp]
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f :=
  X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen ⟨x, hx⟩ f
```

*Mathematical Significance:* A section $f$ evaluates to zero at a point $x$ if and only if $x$ does not lie in the basic open set $D(f)$ where $f$ is invertible. This fundamental result connects the algebraic notion of evaluation with the geometric notion of basic open sets.

This equivalence captures the intuitive idea that a function "vanishes" at a point precisely when that point lies outside the open set where the function is non-zero (and hence invertible).

== Global Evaluation

```lean
abbrev Γevaluation (x : X) : Γ(X, ⊤) ⟶ X.residueField x :=
  X.evaluation ⊤ x trivial
```

*Mathematical Significance:* The global evaluation map takes global sections (functions defined on the entire scheme) and evaluates them at a specific point. This is the scheme-theoretic generalization of the classical notion of evaluating a polynomial at a point.

= Functoriality

== Morphism-Induced Maps

```lean
def Hom.residueFieldMap (f : X.Hom Y) (x : X) :
    Y.residueField (f.base x) ⟶ X.residueField x :=
  CommRingCat.ofHom <| IsLocalRing.ResidueField.map (f.stalkMap x).hom
```

*Mathematical Significance:* A morphism $f: X \to Y$ induces a map of residue fields in the opposite direction: from $\kappa(f(x))$ to $\kappa(x)$. This contravariant functoriality reflects the fact that morphisms of schemes correspond to pullbacks of functions.

The direction reversal is natural: if $f: X \to Y$ is a morphism and $g$ is a function near $f(x)$ on $Y$, then $f^*g$ is a function near $x$ on $X$, and the values are related by this residue field map.

== Naturality

```lean
@[reassoc]
lemma evaluation_naturality {V : Opens Y} (x : X) (hx : f.base x ∈ V) :
    Y.evaluation V (f.base x) hx ≫ f.residueFieldMap x =
      f.app V ≫ X.evaluation (f ^{-1}U V) x hx :=
  LocallyRingedSpace.evaluation_naturality f.1 ⟨x, hx⟩
```

*Mathematical Significance:* Evaluation commutes with morphisms in the natural way: evaluating a section on $Y$ at $f(x)$ and then pulling back to $X$ gives the same result as pulling back the section to $X$ and then evaluating at $x$.

This naturality is crucial for ensuring that evaluation behaves consistently across morphisms and reflects the functorial nature of the residue field construction.

= Canonical Morphisms

== From Spec of Residue Field

```lean
def fromSpecResidueField (X : Scheme) (x : X) :
    Spec (X.residueField x) ⟶ X :=
  Spec.map (X.residue x) ≫ X.fromSpecStalk x
```

*Mathematical Significance:* For any point $x$ in a scheme $X$, there is a canonical morphism from $\mathrm{Spec}(\kappa(x))$ to $X$. This morphism represents the "inclusion of the point" and is fundamental for understanding how points embed into schemes.

The construction factors through the spectrum of the stalk, reflecting the algebraic relationship between the residue field and the local ring at the point.

== Properties of the Canonical Morphism

```lean
@[simp]
lemma fromSpecResidueField_apply (x : X.carrier) (s : Spec (X.residueField x)) :
    (X.fromSpecResidueField x).base s = x := by
  simp [fromSpecResidueField]
```

*Mathematical Significance:* The canonical morphism from $\mathrm{Spec}(\kappa(x))$ to $X$ maps every point of the spectrum (which consists of a single point since $\kappa(x)$ is a field) to the original point $x$. This formalizes the idea that $\mathrm{Spec}(\kappa(x))$ represents the "infinitesimal neighborhood" of $x$.

= Universal Property

== Morphisms from Spectra of Fields

```lean
def SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec(K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where
  toFun f :=
    ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
```

*Mathematical Significance:* This establishes a fundamental bijection: morphisms from the spectrum of a field $K$ to a scheme $X$ correspond bijectively to pairs consisting of a point $x \in X$ and a field homomorphism $\kappa(x) \to K$.

This universal property is crucial for understanding rational points and provides the scheme-theoretic foundation for the classical notion of "points with values in a field."

For example:
\item Rational points (over $\mathbb{Q*$) correspond to morphisms $\mathrm{Spec}(\mathbb{Q}) \to X$
\item Points over finite fields correspond to morphisms $\mathrm{Spec*(\mathbb{F}_q) \to X$
\item Complex points correspond to morphisms $\mathrm{Spec*(\mathbb{C}) \to X$

= Geometric Interpretation

== Classical Correspondence

In classical algebraic geometry over algebraically closed fields, residue fields are typically trivial (isomorphic to the base field). However, in more general settings:

\item *Rational Points*: For schemes over $\mathbb{Q}$, residue fields capture the "field of definition" of each point
\item *Finite Fields*: For schemes over finite fields, residue fields determine the degree of field extensions needed to define points
\item *Arithmetic Geometry*: Residue fields encode crucial arithmetic information about how points are defined over various fields

== Local Nature

The residue field captures the most refined local information about a scheme at a point:

\item *Dimension*: The transcendence degree of the residue field over the base field gives local dimension information
\item *Smoothness*: Properties of the residue field help detect singularities and smooth points
\item *Separability*: The separability of residue field extensions captures geometric properties like étaleness

== Functoriality and Base Change

The contravariant functoriality of residue fields reflects fundamental properties:

\item *Pullback Nature*: Morphisms correspond to pullbacks of functions, hence the contravariance
\item *Base Change*: Residue fields behave well under base change, preserving geometric properties
\item *Galois Theory*: Residue field extensions encode Galois-theoretic information about the geometry

= Applications

== Rational Points

The residue field theory provides the foundation for studying rational points on schemes:

\item Points with residue field isomorphic to the base field correspond to "rational points"
\item Extensions of residue fields correspond to points defined over field extensions
\item The degree of the residue field extension measures the "complexity" of defining the point

== Dimension Theory

Residue fields play a crucial role in dimension theory:

\item The Krull dimension of a scheme can be computed using residue field transcendence degrees
\item Chains of specializations correspond to towers of residue field extensions
\item Dimension inequalities often involve residue field properties

== Morphism Properties

Many properties of morphisms can be detected through their behavior on residue fields:

\item *Finite morphisms*: Correspond to finite residue field extensions
\item *Étale morphisms*: Correspond to separable residue field extensions of the same transcendence degree
\item *Smooth morphisms*: Have well-behaved residue field extensions with controlled ramification

The residue field construction thus provides a fundamental bridge between local algebraic data and global geometric properties, making it an essential tool in modern algebraic geometry.
