#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Pullbacks.lean* file in Mathlib4. The file constructs fibered products (pullbacks) of schemes using gluing techniques, following Hartshorne's Theorem 3.3. The construction shows how to build pullbacks for arbitrary schemes by reducing to the affine case through open covers.

= Main Construction Strategy

== The Gluing Approach

The fundamental idea is to construct pullbacks via gluing:
\item Given schemes $X$, $Y$, $Z$ and morphisms $f: X \to Z$, $g: Y \to Z$
\item For an open cover $\{U_i\*$ of $X$, if pullbacks $U_i \times_Z Y$ exist
\item Then we can glue these pullbacks to construct $X \times_Z Y$

This reduces the problem to the affine case, where pullbacks are constructed via tensor products of rings.

= The Pullback Namespace

== Intersection Schemes

```lean
def v (i j : 𝒰.J) : Scheme :=
  pullback ((pullback.fst (𝒰.map i ≫ f) g) ≫ 𝒰.map i) (𝒰.map j)
```

*Natural Language:* For indices $i, j$ in an open cover, $V_{ij}$ represents the intersection of $U_i \times_Z Y$ and $U_j \times_Z Y$ over $X$. This is constructed as the pullback of the natural maps.

== Transition Maps

```lean
def t (i j : 𝒰.J) : v 𝒰 f g i j ⟶ v 𝒰 f g j i
```

*Natural Language:* The transition map $t_{ij}: V_{ij} \to V_{ji}$ is the canonical isomorphism given by the symmetry and associativity of pullbacks. This ensures that the intersections can be consistently glued.

== Properties of Transition Maps

```lean
theorem t_id (i : 𝒰.J) : t 𝒰 f g i i = 𝟙 _
```

*Natural Language:* The transition map from $V_{ii}$ to itself is the identity morphism.

= The Gluing Data Structure

== The Main Gluing Construction

```lean
def gluing : Scheme.GlueData.{u} where
  J := 𝒰.J
  U i := pullback (𝒰.map i ≫ f) g
  V := fun ⟨i, j⟩ => v 𝒰 f g i j
  f _ _ := pullback.fst _ _
  t i j := t 𝒰 f g i j
  cocycle i j k := cocycle 𝒰 f g i j k
```

*Natural Language:* This constructs the gluing data needed to create the fibered product. The schemes $U_i = U_i \times_Z Y$ are glued together using the intersection schemes $V_{ij}$ and transition maps $t_{ij}$.

== Cocycle Condition

```lean
theorem cocycle (i j k : 𝒰.J) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j = 𝟙 _
```

*Natural Language:* The composition of transition maps around a triple satisfies the cocycle condition, ensuring that the gluing is well-defined.

= Projection Morphisms

== First Projection

```lean
def p1 : (gluing 𝒰 f g).glued ⟶ X
```

*Natural Language:* The first projection $p_1: X \times_Z Y \to X$ is obtained by gluing the natural projections from each $U_i \times_Z Y$ to $U_i \subseteq X$.

== Second Projection

```lean
def p2 : (gluing 𝒰 f g).glued ⟶ Y
```

*Natural Language:* The second projection $p_2: X \times_Z Y \to Y$ is obtained by gluing the natural projections from each $U_i \times_Z Y$ to $Y$.

== Pullback Square Property

```lean
theorem p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g
```

*Natural Language:* The glued scheme forms a pullback square: $p_1 \circ f = p_2 \circ g$, confirming that we have constructed the fibered product correctly.

= Universal Property

== Lifting Property

```lean
def gluedLift : s.pt ⟶ (gluing 𝒰 f g).glued
```

*Natural Language:* Given any pullback cone $s$ for the diagram $X \leftarrow Z \rightarrow Y$, there exists a unique morphism from the apex of $s$ to the glued pullback.

== Main Theorem: Glued Pullback is a Limit

```lean
def gluedIsLimit : IsLimit (PullbackCone.mk _ _ (p_comm 𝒰 f g))
```

*Natural Language:* The glued construction satisfies the universal property of pullbacks, making it the categorical pullback (fibered product) in the category of schemes.

= Special Cases and Applications

== Affine-Affine Pullbacks

```lean
instance affine_hasPullback {A B C : CommRingCat}
    (f : Spec A ⟶ Spec C)
    (g : Spec B ⟶ Spec C) : HasPullback f g
```

*Natural Language:* When all schemes are affine, pullbacks exist and are computed using the tensor product construction in commutative rings.

== General Existence

```lean
instance : HasPullbacks Scheme
```

*Natural Language:* The category of schemes has all pullbacks. This is proven using the gluing construction applied to affine covers.

= Spectrum Tensor Product Isomorphism

== The Main Isomorphism

```lean
def pullbackSpecIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec(S ⊗[R] T)
```

*Natural Language:* For commutative rings $R$, $S$, $T$ with algebra structures, the pullback of $\mathrm{Spec}(S) \to \mathrm{Spec}(R) \leftarrow \mathrm{Spec}(T)$ is isomorphic to $\mathrm{Spec}(S \otimes_R T)$.

== Projection Formulas

```lean
lemma pullbackSpecIso_inv_fst :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom includeLeftRingHom)
```

*Natural Language:* The first projection corresponds to the ring homomorphism $s \mapsto s \otimes 1$ from $S$ to $S \otimes_R T$.

= Open Covers of Pullbacks

== Cover by Left Components

```lean
def openCoverOfLeft (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g)
```

*Natural Language:* Given an open cover $\{U_i\}$ of $X$, the pullback $X \times_Z Y$ is covered by the schemes $U_i \times_Z Y$.

== Cover by Both Components

```lean
def openCoverOfLeftRight (𝒰X : X.OpenCover) (𝒰Y : Y.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).OpenCover
```

*Natural Language:* Given open covers of both $X$ and $Y$, the pullback is covered by all pairwise products $U_i \times_Z V_j$.

= Geometric Properties

== Preservation of Affine Property

```lean
instance isAffine_of_isAffine_isAffine_isAffine {X Y Z : Scheme}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffine X] [IsAffine Y] [IsAffine Z] :
    IsAffine (pullback f g)
```

*Natural Language:* The pullback of affine schemes over an affine base is affine. This follows from the tensor product construction for affine schemes.

== Empty Pullbacks

```lean
theorem _root_.AlgebraicGeometry.Scheme.isEmpty_pullback
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (H : Disjoint (Set.range f.base) (Set.range g.base)) : IsEmpty ↑(Limits.pullback f g)
```

*Natural Language:* If the images of $f$ and $g$ are disjoint in $S$, then the pullback is empty.

= Applications to Cartesian Monoidal Structure

== Cartesian Structure on Over Categories

```lean
instance : CartesianMonoidalCategory (Over S)
```

*Natural Language:* The existence of pullbacks gives the category of $S$-schemes a cartesian monoidal structure, where the tensor product is the pullback over $S$.

= Conclusion

The pullback construction in `Pullbacks.lean* provides:
\item A systematic way to construct fibered products of arbitrary schemes
\item Reduction of the general case to the well-understood affine case
\item Complete proof that the category of schemes has all pullbacks
\item Explicit constructions for various special cases and covers
\item Foundation for cartesian monoidal structure in algebraic geometry

This construction is fundamental to many areas of algebraic geometry, including base change, families of schemes, and moduli theory.
