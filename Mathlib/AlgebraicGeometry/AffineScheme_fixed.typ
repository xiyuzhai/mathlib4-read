#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

// Define a custom code block for Lean code with syntax highlighting
#let leancode(code) = {
  block(
    fill: luma(245),
    inset: 8pt,
    radius: 4pt,
    width: 100%,
    raw(code, lang: "lean", block: true)
  )
}

= Introduction

This document provides a natural language companion to the AffineScheme.lean file in Mathlib4. The file defines affine schemes as the essential image of the Spec functor and establishes key properties about affine schemes and affine open sets.

= Main Definitions

== The Category of Affine Schemes

#leancode("def AffineScheme :=
  Scheme.Spec.EssImageSubcategory
deriving Category")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The category of affine schemes is defined as the essential image subcategory of the Spec functor. This captures precisely those schemes that are isomorphic to spectra of commutative rings.

== The IsAffine Property

#leancode("class IsAffine (X : Scheme) : Prop where
  affine : IsIso X.toSpecΓ")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* A scheme $X$ is affine if and only if the canonical morphism $X \to op("Spec")(Gamma(X, top))$ is an isomorphism, where $Gamma(X, top)$ denotes the global sections of the structure sheaf.

== The Canonical Isomorphism for Affine Schemes

#leancode("def Scheme.isoSpec (X : Scheme) [IsAffine X] :
  X ≅ Spec Γ(X, ⊤) := asIso X.toSpecΓ")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* For any affine scheme $X$, there exists a canonical isomorphism between $X$ and the spectrum of its global sections.

= Key Theorems

== Naturality of the Spec Isomorphism

#leancode("theorem Scheme.isoSpec_hom_naturality {X Y : Scheme}
  [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
  X.isoSpec.hom ≫ Spec.map (f.appTop) = f ≫ Y.isoSpec.hom")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The canonical isomorphisms to spectra are natural with respect to morphisms between affine schemes. This means the diagram commutes when we map between affine schemes and their corresponding spectra.

== Uniqueness of Morphisms via Global Sections

#leancode("lemma ext_of_isAffine {X Y : Scheme} [IsAffine Y]
  {f g : X ⟶ Y} (e : f.appTop = g.appTop) : f = g")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* Two morphisms into an affine scheme are equal if and only if they induce the same map on global sections. This reflects the fact that morphisms into affine schemes are completely determined by their behavior on global sections.

= The Equivalence of Categories

== The Spec Functor

#leancode("def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The Spec functor maps from the opposite category of commutative rings to affine schemes. This is the restriction of the usual Spec functor to its essential image.

== The Global Sections Functor

#leancode("def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The global sections functor $Gamma$ maps from the opposite category of affine schemes to commutative rings by taking the global sections of the structure sheaf.

== The Main Equivalence

#leancode("def equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The category of affine schemes is equivalent to the opposite category of commutative rings. This is the fundamental duality between algebra and geometry in the affine case.

= Affine Open Sets

== Definition of Affine Opens

#leancode("def IsAffineOpen {X : Scheme} (U : X.Opens) : Prop :=
  IsAffine U")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* An open subset $U$ of a scheme $X$ is called affine if the corresponding open subscheme is an affine scheme.

== The Set of Affine Opens

#leancode("def Scheme.affineOpens (X : Scheme) : Set X.Opens :=
  {U : X.Opens | IsAffineOpen U}")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* For any scheme $X$, we can consider the collection of all affine open subsets, which forms a set in the opens of $X$.

= Properties of Affine Opens

== Affine Opens Form a Basis

#leancode("theorem isBasis_affine_open (X : Scheme) :
  Opens.IsBasis X.affineOpens")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The affine open subsets form a topological basis for any scheme. This means every open set can be written as a union of affine opens.

== Coverage by Affine Opens

#leancode("theorem iSup_affineOpens_eq_top (X : Scheme) :
  ⨆ i : X.affineOpens, (i : X.Opens) = ⊤")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* Every scheme can be covered by affine open subsets. The supremum (union) of all affine opens equals the entire scheme.

== Existence of Affine Neighborhoods

#leancode("theorem exists_isAffineOpen_mem_and_subset {X : Scheme.{u}}
  {x : X} {U : X.Opens} (hxU : x ∈ U) :
  ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W.1 ⊆ U")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* For any point $x$ in an open set $U$ of a scheme, there exists an affine open neighborhood $W$ of $x$ contained in $U$.

= The IsAffineOpen Structure

== The Canonical Isomorphism for Affine Opens

#leancode("def isoSpec : ↑U ≅ Spec Γ(X, U) :=
  haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* For an affine open $U$ of a scheme $X$, there is a canonical isomorphism between $U$ (viewed as a scheme) and the spectrum of the sections over $U$.

== The fromSpec Morphism

#leancode("def fromSpec : Spec Γ(X, U) ⟶ X :=
  haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* For an affine open $U$, we have a canonical open immersion from $op("Spec")(Gamma(X, U))$ into $X$ whose image is precisely $U$.

== Range of fromSpec

#leancode("theorem range_fromSpec :
  Set.range hU.fromSpec.base = (U : Set X)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The image of the fromSpec morphism is exactly the open set $U$ as a subset of $X$.

= Preservation of Affine Opens

== Image Under Open Immersions

#leancode("theorem image_of_isOpenImmersion (f : X ⟶ Y)
  [H : IsOpenImmersion f] : IsAffineOpen (f ^U U)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The image of an affine open under an open immersion is again affine open.

== Preimage Under Isomorphisms

#leancode("theorem preimage_of_isIso {U : Y.Opens} (hU : IsAffineOpen U)
  (f : X ⟶ Y) [IsIso f] : IsAffineOpen (f ^{-1}U U)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The preimage of an affine open under an isomorphism is affine open.

= Compactness Properties

== Affine Opens are Quasi-Compact

#leancode("protected theorem isCompact : IsCompact (U : Set X)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* Every affine open subset is quasi-compact (compact in the scheme-theoretic sense).

== Affine Schemes are Quasi-Compact

#leancode("instance Scheme.compactSpace_of_isAffine (X : Scheme)
  [IsAffine X] : CompactSpace X")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* Every affine scheme is quasi-compact as a topological space.

= Basic Opens in Affine Schemes

#leancode("theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
  Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) → X.Opens))")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* In an affine scheme, the basic open sets (corresponding to principal open subsets in the spectrum) form a topological basis.

== Basic Opens are Affine

#leancode("instance [IsAffine X] (r : Γ(X, ⊤)) : IsAffine (X.basicOpen r)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* If $X$ is an affine scheme and $r$ is a global section, then the basic open set $D(r)$ is also affine. This is the scheme-theoretic analog of the fact that localizations of rings give affine schemes.

= Localization Properties

== Basic Opens and Localizations

#leancode("theorem isLocalization_basicOpen :
  IsLocalization.Away f Γ(X, X.basicOpen f)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The sections over a basic open set $D(f)$ form the localization of the global sections away from $f$. This establishes the fundamental connection between geometric opens and algebraic localizations.

== Stalk Localization

#leancode("theorem isLocalization_stalk (x : U) :
  IsLocalization.AtPrime
    (X.presheaf.stalk x)
    (hU.primeIdealOf x).asIdeal")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The stalk at a point $x$ in an affine open $U$ is the localization of $Gamma(X, U)$ at the corresponding prime ideal. This provides the local-to-global principle for affine opens.

= The Spec Target Image

== Image Ideal for Morphisms to Spec

#leancode("def specTargetImageIdeal (f : X ⟶ Spec A) : Ideal A :=
  Ideal.span (Set.range f.appTop)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* For a morphism $f: X \to op("Spec")(A)$, the target image ideal is the ideal generated by the image of the map on global sections.

== Factorization Through the Image

#leancode("def specTargetImageFactorization (f : X ⟶ Spec A) :
  X ⟶ Spec (specTargetImage f)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* Any morphism to a spectrum factors through the spectrum of its target image ring, which is the quotient by the kernel of the induced ring homomorphism.

= Lifting and Quotient Properties

== Lifting Morphisms Through Quotients

#leancode("def Scheme.Hom.liftQuotient (f : X.Hom (Spec A)) (I : Ideal A)
  (h : ∀ x : X, f.base x ∈ (PrimeSpectrum.zeroLocus I : Set)) :
  X.Hom (Spec (A ⧸ I))")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* A morphism $f: X \to op("Spec")(A)$ whose image lies in the zero locus of an ideal $I$ can be lifted to a morphism $X \to op("Spec")(A/I)$.

= Zero Locus and Closed Sets

== Characterization of Closed Sets in Affine Schemes

#leancode("lemma eq_zeroLocus_of_isClosed_of_isAffine [IsAffine X] (s : Set X) :
  IsClosed s ↔ ∃ I : Ideal Γ(X, ⊤), s = X.zeroLocus I")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* In an affine scheme, every closed set is the zero locus of some ideal in the global sections. This establishes the correspondence between closed sets and radical ideals.

== Preimage of Zero Locus

#leancode("lemma toSpecΓ_preimage_zeroLocus (s : Set Γ(X, ⊤)) :
  X.toSpecΓ.base ⁻¹' PrimeSpectrum.zeroLocus s =
  X.zeroLocus (Ideal.span s)")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* The preimage of a zero locus under the canonical morphism to the spectrum is the zero locus of the ideal generated by the corresponding sections.

= Union and Intersection Properties

== Basic Opens Generate the Topology

#leancode("theorem basicOpen_union_eq_self_iff (s : Set Γ(X, U)) :
  ⨆ f : s, X.basicOpen f.1 = U ↔
  Ideal.span s = ⊤")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* A collection of basic opens covers an affine open $U$ if and only if the corresponding sections generate the unit ideal. This is the geometric manifestation of the fact that elements generate the unit ideal if and only if they have no common zeros.

== Supremum of Basic Opens

#leancode("lemma iSup_basicOpen_of_span_eq_top {X : Scheme} (U) (s : Set Γ(X, U))
  (hs : Ideal.span s = ⊤) : ⨆ f : s, X.basicOpen f.1 = U")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* If sections generate the unit ideal, then their corresponding basic opens cover the entire affine open.

= Properties of Affine Open Covers

== Local Properties on Affine Opens

#leancode("theorem of_affine_open_cover {X : Scheme} {P : X.affineOpens → Prop}
  (hP : ∀ (U : X.affineOpens) (f : Γ(X, U)) (hf : X.basicOpen f ≤ U),
    P ⟨X.basicOpen f, (U : X.Opens).isAffineOpen.basicOpen f⟩ →
    P U)
  (hP' : ∀ (U : X.affineOpens) (s : Finset Γ(X, U))
    (hs : Ideal.span (s : Set Γ(X, U)) = ⊤),
    (∀ f : s, P ⟨X.basicOpen f.1, (U : X.Opens).isAffineOpen.basicOpen f⟩) →
    P U)
  (U : X.affineOpens) : P U")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[
*Natural Language:* Properties of affine opens can be established by checking them on basic opens and using the fact that basic opens form a basis. This provides a powerful induction principle for proving statements about all affine opens.

= Categorical Properties

== Limits and Colimits

#leancode("instance hasColimits : HasColimits AffineScheme.{u}
instance hasLimits : HasLimits AffineScheme.{u}")
#block(fill: luma(245), inset: 8pt, radius: 4pt)[

*Natural Language:* The category of affine schemes has all limits and colimits. These are computed via the equivalence with the opposite category of commutative rings.

== Fullness and Faithfulness

*Lean Code:*

#raw("instance Spec_full : Spec.Full")

#raw("instance Spec_faithful : Spec.Faithful")

#raw("instance Spec_essSurj : Spec.EssSurj")

*Natural Language:* The Spec functor is fully faithful and essentially surjective, establishing that it gives an equivalence of categories between commutative rings (with reversed arrows) and affine schemes.
