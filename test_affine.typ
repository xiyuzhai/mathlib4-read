#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `AffineScheme.lean* file in Mathlib4. The file defines affine schemes as the essential image of the Spec functor and establishes key properties about affine schemes and affine open sets.

= Main Definitions

== The Category of Affine Schemes

```lean
def AffineScheme :=
  Scheme.Spec.EssImageSubcategory
deriving Category
```

*Natural Language:* The category of affine schemes is defined as the essential image subcategory of the Spec functor. This captures precisely those schemes that are isomorphic to spectra of commutative rings.

== The IsAffine Property

```lean
class IsAffine (X : Scheme) : Prop where
  affine : IsIso X.toSpecΓ
```

*Natural Language:* A scheme $X$ is affine if and only if the canonical morphism $X \to \mathrm{Spec}(\Gamma(X, \top))$ is an isomorphism, where $\Gamma(X, \top)$ denotes the global sections of the structure sheaf.

== The Canonical Isomorphism for Affine Schemes

```lean
def Scheme.isoSpec (X : Scheme) [IsAffine X] :
  X ≅ Spec Γ(X, ⊤) := asIso X.toSpecΓ
```

*Natural Language:* For any affine scheme $X$, there exists a canonical isomorphism between $X$ and the spectrum of its global sections.

= Key Theorems

== Naturality of the Spec Isomorphism

```lean
theorem Scheme.isoSpec_hom_naturality {X Y : Scheme}
  [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
  X.isoSpec.hom ≫ Spec.map (f.appTop) = f ≫ Y.isoSpec.hom
```

*Natural Language:* The canonical isomorphisms to spectra are natural with respect to morphisms between affine schemes. This means the diagram commutes when we map between affine schemes and their corresponding spectra.

== Uniqueness of Morphisms via Global Sections

```lean
lemma ext_of_isAffine {X Y : Scheme} [IsAffine Y]
  {f g : X ⟶ Y} (e : f.appTop = g.appTop) : f = g
```

*Natural Language:* Two morphisms into an affine scheme are equal if and only if they induce the same map on global sections. This reflects the fact that morphisms into affine schemes are completely determined by their behavior on global sections.

= The Equivalence of Categories

== The Spec Functor

```lean
def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage
```

*Natural Language:* The Spec functor maps from the opposite category of commutative rings to affine schemes. This is the restriction of the usual Spec functor to its essential image.

== The Global Sections Functor

```lean
def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ
```

*Natural Language:* The global sections functor $\Gamma$ maps from the opposite category of affine schemes to commutative rings by taking the global sections of the structure sheaf.

== The Main Equivalence

```lean
def equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm
```

*Natural Language:* The category of affine schemes is equivalent to the opposite category of commutative rings. This is the fundamental duality between algebra and geometry in the affine case.

= Affine Open Sets

== Definition of Affine Opens

```lean
def IsAffineOpen {X : Scheme} (U : X.Opens) : Prop :=
  IsAffine U
```

*Natural Language:* An open subset $U$ of a scheme $X$ is called affine if the corresponding open subscheme is an affine scheme.

== The Set of Affine Opens

```lean
def Scheme.affineOpens (X : Scheme) : Set X.Opens :=
  {U : X.Opens | IsAffineOpen U}
```

*Natural Language:* For any scheme $X$, we can consider the collection of all affine open subsets, which forms a set in the opens of $X$.

= Properties of Affine Opens

== Affine Opens Form a Basis

```lean
theorem isBasis_affine_open (X : Scheme) :
  Opens.IsBasis X.affineOpens
```

*Natural Language:* The affine open subsets form a topological basis for any scheme. This means every open set can be written as a union of affine opens.

== Coverage by Affine Opens

```lean
theorem iSup_affineOpens_eq_top (X : Scheme) :
  ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
```

*Natural Language:* Every scheme can be covered by affine open subsets. The supremum (union) of all affine opens equals the entire scheme.

== Existence of Affine Neighborhoods

```lean
theorem exists_isAffineOpen_mem_and_subset {X : Scheme.{u}}
  {x : X} {U : X.Opens} (hxU : x ∈ U) :
  ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W.1 ⊆ U
```

*Natural Language:* For any point $x$ in an open set $U$ of a scheme, there exists an affine open neighborhood $W$ of $x$ contained in $U$.

= The IsAffineOpen Structure

== The Canonical Isomorphism for Affine Opens

```lean
def isoSpec : ↑U ≅ Spec Γ(X, U) :=
  haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op
```

*Natural Language:* For an affine open $U$ of a scheme $X$, there is a canonical isomorphism between $U$ (viewed as a scheme) and the spectrum of the sections over $U$.

== The fromSpec Morphism

```lean
def fromSpec : Spec Γ(X, U) ⟶ X :=
  haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι
```

*Natural Language:* For an affine open $U$, we have a canonical open immersion from $\mathrm{Spec}(\Gamma(X, U))$ into $X$ whose image is precisely $U$.

== Range of fromSpec

```lean
theorem range_fromSpec :
  Set.range hU.fromSpec.base = (U : Set X)
```

*Natural Language:* The image of the fromSpec morphism is exactly the open set $U$ as a subset of $X$.

= Preservation of Affine Opens

== Image Under Open Immersions

```lean
theorem image_of_isOpenImmersion (f : X ⟶ Y)
  [H : IsOpenImmersion f] : IsAffineOpen (f ^U U)
```

*Natural Language:* The image of an affine open under an open immersion is again affine open.

== Preimage Under Isomorphisms

```lean
theorem preimage_of_isIso {U : Y.Opens} (hU : IsAffineOpen U)
  (f : X ⟶ Y) [IsIso f] : IsAffineOpen (f ^{-1}U U)
```

*Natural Language:* The preimage of an affine open under an isomorphism is affine open.

= Compactness Properties

== Affine Opens are Quasi-Compact

```lean
protected theorem isCompact : IsCompact (U : Set X)
```

*Natural Language:* Every affine open subset is quasi-compact (compact in the scheme-theoretic sense).

== Affine Schemes are Quasi-Compact
