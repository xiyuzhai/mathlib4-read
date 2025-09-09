#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Restrict.lean* file in Mathlib4. The file develops the theory of restricting schemes to open subsets and restricting morphisms accordingly. This is fundamental to the local nature of algebraic geometry, where properties are often studied by restricting to smaller open sets.

= Open Subsets as Schemes

== Coercion to Schemes

```lean
@[coe]
def toScheme {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} :=
  X.restrict U.isOpenEmbedding

instance : CoeOut X.Opens Scheme := ⟨toScheme⟩
```

*Natural Language:* Every open subset $U$ of a scheme $X$ can be viewed as a scheme in its own right through the restriction construction. This creates a coercion that allows us to treat opens as schemes directly.

== The Inclusion Morphism

```lean
def ι : ↑U ⟶ X := X.ofRestrict _
```

*Natural Language:* For each open subset $U \subseteq X$, there is a canonical inclusion morphism $\iota: U \to X$ that embeds $U$ as an open subscheme of $X$.

== Open Immersion Property

```lean
instance : IsOpenImmersion U.ι
```

*Natural Language:* The inclusion morphism $U \to X$ is an open immersion, meaning it identifies $U$ with its image as an open subset and preserves the scheme structure.

= Presheaf Properties

== Presheaf Objects

```lean
lemma toScheme_presheaf_obj (V) : Γ(U, V) = Γ(X, U.ι ^U V)
```

*Natural Language:* Sections over an open set $V$ in the restricted scheme $U$ correspond exactly to sections over the image $U.\iota(V)$ in the original scheme $X$.

== Presheaf Maps

```lean
@[simp]
lemma toScheme_presheaf_map {V W} (i : V ⟶ W) :
    U.toScheme.presheaf.map i = X.presheaf.map (U.ι.opensFunctor.map i.unop).op
```

*Natural Language:* Restriction maps in the presheaf on $U$ are obtained by pushing forward along $\iota$ to get restriction maps in the presheaf on $X$.

= Application Maps

== Basic Application

```lean
@[simp]
lemma ι_app (V) : U.ι.app V = X.presheaf.map
    (homOfLE (x := U.ι ^U U.ι ^{-1}U V) (Set.image_preimage_subset _ _)).op
```

*Natural Language:* The application of $\iota$ to sections is given by the natural restriction map in $X$'s presheaf.

== Top Application

```lean
@[simp]
lemma ι_appTop :
    U.ι.appTop = X.presheaf.map (homOfLE (x := U.ι ^U ⊤) le_top).op
```

*Natural Language:* Taking global sections of $U$ corresponds to taking sections of $X$ over the image of $U$.

= Range Properties

== Opens Range

```lean
@[simp]
lemma opensRange_ι : U.ι.opensRange = U
```

*Natural Language:* The image of $\iota$ as an open subset is exactly $U$ itself.

== Topological Range

```lean
@[simp]
lemma range_ι : Set.range U.ι.base = U
```

*Natural Language:* The image of the underlying continuous map is exactly the subset $U \subseteq X$.

= Global Sections Isomorphism

== Top Isomorphism

```lean
@[simps!]
def topIso : Γ(U, ⊤) ≅ Γ(X, U) :=
  X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
```

*Natural Language:* The global sections of the restricted scheme $U$ are naturally isomorphic to the sections of $X$ over the open set $U$. This establishes the fundamental relationship between restriction and sections.

= Stalks

== Stalk Isomorphism

```lean
def stalkIso {X : Scheme.{u}} (U : X.Opens) (x : U) :
    U.toScheme.presheaf.stalk x ≅ X.presheaf.stalk x.1
```

*Natural Language:* The stalk of the structure sheaf of $U$ at a point $x$ is naturally isomorphic to the stalk of $X$'s structure sheaf at the same point. This shows that local properties are preserved under restriction.

== Germ Compatibility

```lean
@[reassoc (attr := simp)]
lemma germ_stalkIso_hom {X : Scheme.{u}} (U : X.Opens)
    {V : U.toScheme.Opens} (x : U) (hx : x ∈ V) :
      U.toScheme.presheaf.germ V x hx ≫ (U.stalkIso x).hom =
        X.presheaf.germ (U.ι ^U V) x.1 ⟨x, hx, rfl⟩
```

*Natural Language:* Germs (local sections) behave compatibly with the stalk isomorphism, ensuring that the restriction preserves all local algebraic structure.

= Restriction Functors and Equivalences

== Opens Restriction

```lean
@[simps!]
def opensRestrict :
    Scheme.Opens U ≃ { V : X.Opens // V ≤ U }
```

*Natural Language:* Open subsets of the restricted scheme $U$ correspond bijectively to open subsets of $X$ that are contained in $U$.

== Restrict Functor

```lean
@[simps! obj_left obj_hom map_left]
def Scheme.restrictFunctor : X.Opens ⥤ Over X where
  obj U := Over.mk U.ι
  map {U V} i := Over.homMk (X.homOfLE i.le) (by simp)
```

*Natural Language:* There is a functor from the category of opens of $X$ to schemes over $X$, sending each open $U$ to the restricted scheme $U \to X$.

= Morphisms Between Opens

== Inclusion of Smaller Opens

```lean
protected noncomputable
def Scheme.homOfLE (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) : (U : Scheme.{u}) ⟶ V
```

*Natural Language:* If $U \subseteq V$ are open subsets of $X$, there is a natural morphism from the scheme $U$ to the scheme $V$.

== Compatibility with Inclusion

```lean
@[reassoc (attr := simp)]
lemma Scheme.homOfLE_ι (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) :
    X.homOfLE e ≫ V.ι = U.ι
```

*Natural Language:* The composition $U \to V \to X$ equals the direct inclusion $U \to X$.

= Basic Opens and Localizations

== Basic Open Mapping

```lean
lemma Scheme.map_basicOpen (r : Γ(U, ⊤)) :
    U.ι ^U U.toScheme.basicOpen r = X.basicOpen
      (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top.symm).op r)
```

*Natural Language:* The image under $\iota$ of a basic open $D(r)$ in $U$ equals a basic open in $X$ determined by the corresponding section.

== Basic Open Isomorphism to Localization

```lean
def basicOpenIsoSpecAway {R : CommRingCat.{u}} (f : R) :
    Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f) ≅ Spec(Localization.Away f)
```

*Natural Language:* For an affine scheme $\mathrm{Spec}(R)$, the basic open $D(f)$ is isomorphic to $\mathrm{Spec}(R[1/f])$, establishing the connection between geometric opens and ring-theoretic localizations.

= Morphism Restriction

== Pullback-Restriction Isomorphism

```lean
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f (U.ι) ≅ f ^{-1}U U
```

*Natural Language:* The pullback of a morphism $f: X \to Y$ along the inclusion $U \to Y$ is isomorphic to the restriction of $X$ to the preimage $f^{-1}(U)$.

== Morphism Restriction Definition

```lean
def morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ^{-1}U U).toScheme ⟶ U :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _

infixl:85 " ∣_ " => morphismRestrict
```

*Natural Language:* Given a morphism $f: X \to Y$ and an open $U \subseteq Y$, we can restrict $f$ to get a morphism $f|_U: f^{-1}(U) \to U$. This uses the notation $f \mid_U$.

= Properties of Morphism Restriction

== Compatibility with Inclusions

```lean
@[reassoc (attr := simp)]
theorem morphismRestrict_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U) ≫ U.ι = (f ^{-1}U U).ι ≫ f
```

*Natural Language:* The restricted morphism is compatible with the inclusion maps in the sense that the diagram commutes.

== Identity Restriction

```lean
@[simp]
lemma morphismRestrict_id {X : Scheme.{u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _ := by
  rw [← cancel_mono U.ι, morphismRestrict_ι, Category.comp_id, Category.id_comp]
```

*Natural Language:* Restricting the identity morphism gives the identity on the restricted scheme.

== Composition Property

```lean
theorem morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) :
    (f ≫ g) ∣_ U = f ∣_ g ^{-1}U U ≫ g ∣_ U
```

*Natural Language:* Restricting a composition of morphisms equals the composition of the appropriate restrictions.

= Base Change Properties

== Continuous Map Base

```lean
theorem morphismRestrict_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    ⇑(f ∣_ U).base = U.1.restrictPreimage f.base
```

*Natural Language:* The underlying continuous map of the restricted morphism is the restriction of the original continuous map to the appropriate preimage.

== Pullback Isomorphism

```lean
theorem isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f ∣_ U) (f ^{-1}U U).ι U.ι f
```

*Natural Language:* The restriction construction gives a genuine pullback square, confirming that it captures the correct universal property.

= Stalk Maps and Localization

== Stalk Map Compatibility

```lean
def morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    Arrow.mk ((f ∣_ U).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1)
```

*Natural Language:* The stalk map of a restricted morphism is naturally isomorphic to the stalk map of the original morphism, showing that local algebraic properties are preserved.

= Advanced Restriction Constructions

== Double Restriction

```lean
def morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.ι ^U V)
```

*Natural Language:* Restricting twice is isomorphic to a single restriction to the appropriate open subset.

== Basic Open Restriction

```lean
def morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    Arrow.mk (f ∣_ U ∣_ U.toScheme.basicOpen (Y.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r)
```

*Natural Language:* Restricting first to an open $U$ and then to a basic open determined by a section on $U$ is isomorphic to restricting directly to the corresponding basic open in $Y$.

= Applications to Covers

== Open Cover Restriction

```lean
@[simps! J obj map]
noncomputable
def Scheme.OpenCover.restrict {X : Scheme.{u}} (𝒰 : X.OpenCover) (U : Opens X) :
    U.toScheme.OpenCover
```

*Natural Language:* Given an open cover of $X$, we can restrict it to get an open cover of any open subset $U \subseteq X$.

= Conclusion

The restriction theory developed in `Restrict.lean* provides:

== Foundational Results

\item Every open subset naturally carries a scheme structure
\item Inclusion morphisms are open immersions
\item Local properties (stalks, germs) are preserved under restriction

== Functorial Properties

\item Restriction gives functors between appropriate categories
\item Global sections of restricted schemes relate naturally to sections on opens
\item Morphisms can be restricted in a way that preserves composition and identities

== Connections to Commutative Algebra

\item Basic opens in affine schemes correspond to localizations
\item Stalks of restricted schemes are unchanged
\item Restriction preserves the local ring structure

== Geometric Applications

\item Provides the foundation for studying local properties of schemes
\item Enables the use of open covers to reduce global problems to local ones
\item Essential for constructions like gluing and descent theory

This restriction theory is fundamental to algebraic geometry, enabling the systematic study of local properties and the construction of schemes via gluing local pieces.
