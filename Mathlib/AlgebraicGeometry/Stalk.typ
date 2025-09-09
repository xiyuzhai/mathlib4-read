#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Stalk.lean* file in Mathlib4. The file develops the theory of stalks for schemes, which are fundamental algebraic objects that capture the local behavior of schemes at individual points. Stalks provide the bridge between the geometric intuition of "local rings of functions at a point" and the algebraic machinery needed for rigorous scheme theory.

In classical algebraic geometry, the stalk at a point corresponds to the localization of the coordinate ring at the prime ideal corresponding to that point. In general scheme theory, stalks are defined as direct limits of sections over neighborhoods of the point, providing a systematic way to study local properties.

The stalk theory is essential for:
\item Understanding the local algebraic structure at each point
\item Defining and studying morphisms between schemes
\item Connecting scheme theory to classical algebraic geometry
\item Developing the theory of coherent sheaves and local properties

= Morphisms from Spec of Stalks

== Definition via Affine Opens

```lean
noncomputable def IsAffineOpen.fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec
```

*Mathematical Significance:* For any affine open neighborhood $U$ of a point $x$, we can construct a canonical morphism from $\mathrm{Spec}(\mathcal{O}_{X,x})$ to $X$. This morphism is built by composing the natural map induced by the germ homomorphism with the canonical inclusion of the affine open.

This construction provides a way to "embed" the spectrum of the stalk (which represents the local algebraic data at $x$) back into the original scheme $X$.

== Independence of Choice

```lean
theorem IsAffineOpen.fromSpecStalk_eq (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X) (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  -- Technical proof showing the constructions agree
```

*Mathematical Significance:* The morphism $\mathrm{Spec}(\mathcal{O}_{X,x}) \to X$ does not depend on the choice of affine open neighborhood used in its construction. This is crucial because it ensures that the construction is well-defined and canonical.

The proof uses the fact that affine opens form a basis for the topology, so any two affine neighborhoods can be refined by a smaller affine neighborhood, and the constructions agree when traced through this refinement.

== Canonical Definition

```lean
noncomputable def Scheme.fromSpecStalk (X : Scheme) (x : X) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  (isAffineOpen_opensRange (X.affineOpenCover.map x)).fromSpecStalk (X.affineOpenCover.covers x)
```

*Mathematical Significance:* Using the independence result, we can define the canonical morphism $\mathrm{Spec}(\mathcal{O}_{X,x}) \to X$ using any convenient affine open neighborhood. The definition uses the affine open cover, but the result is independent of this choice.

This morphism encodes the idea that the spectrum of the stalk represents the "formal neighborhood" of the point $x$ in $X$.

= Properties of the Canonical Morphism

== Closed Point Behavior

```lean
@[simp]
lemma fromSpecStalk_closedPoint {x : X} :
    (X.fromSpecStalk x).base (closedPoint (X.presheaf.stalk x)) = x :=
  IsAffineOpen.fromSpecStalk_closedPoint _ _
```

*Mathematical Significance:* The morphism $\mathrm{Spec}(\mathcal{O}_{X,x}) \to X$ maps the closed point of the stalk spectrum (corresponding to the maximal ideal of $\mathcal{O}_{X,x}$) to the original point $x$. This formalizes the intuitive idea that the stalk "sits at" the point $x$.

== Preimmersion Property

```lean
instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecStalk x) :=
  IsAffineOpen.fromSpecStalk_isPreimmersion _ _ _
```

*Mathematical Significance:* The canonical morphism from $\mathrm{Spec}(\mathcal{O}_{X,x})$ to $X$ is a preimmersion, which means it is a composition of an open immersion followed by a closed immersion. This ensures that the morphism has good geometric properties and behaves well with respect to the topology.

= Range and Specialization

== Range Characterization

```lean
@[stacks 01J7]
lemma range_fromSpecStalk {x : X} :
    Set.range (X.fromSpecStalk x).base = { y | y ⤳ x } := by
```

*Mathematical Significance:* The image of the morphism $\mathrm{Spec}(\mathcal{O}_{X,x}) \to X$ consists exactly of those points $y$ that specialize to $x$ (written $y \leadsto x$). This provides a beautiful geometric interpretation: the spectrum of the stalk parametrizes all the ways points can specialize to $x$.

In classical terms, if $x$ corresponds to a prime ideal $\mathfrak{p*$, then the points specializing to $x$ correspond to prime ideals contained in $\mathfrak{p}$, which is exactly what the spectrum of the localization $R_\mathfrak{p}$ parametrizes.

== Compatibility with Specialization

```lean
@[reassoc (attr := simp)]
lemma Spec_map_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x := by
```

*Mathematical Significance:* If $x$ specializes to $y$, then there is a natural map of stalks $\mathcal{O}_{X,y} \to \mathcal{O}_{X,x}$, and the induced map $\mathrm{Spec}(\mathcal{O}_{X,x}) \to \mathrm{Spec}(\mathcal{O}_{X,y})$ is compatible with the fromSpecStalk morphisms.

This compatibility ensures that the stalk construction behaves functorially with respect to specializations and maintains the geometric relationships between points.

= Functoriality

== Compatibility with Morphisms

```lean
@[reassoc (attr := simp)]
lemma Spec_map_stalkMap_fromSpecStalk {x} :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecStalk x ≫ f := by
```

*Mathematical Significance:* For a morphism $f: X \to Y$ and a point $x \in X$, the natural diagram involving stalk maps and fromSpecStalk morphisms commutes. This fundamental compatibility ensures that the stalk construction is functorial and preserves the relationships established by scheme morphisms.

The commutativity expresses the fact that we can either:
\item Map the stalk and then apply fromSpecStalk, or
\item Apply fromSpecStalk and then apply the original morphism
and get the same result.

= Local Rings and Closed Points

== Stalk-Closed Point Isomorphism

```lean
noncomputable
def stalkClosedPointIso :
    (Spec R).presheaf.stalk (closedPoint R) ≅ R :=
  StructureSheaf.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ ↦ not_not.mp).toRingEquiv.toCommRingCatIso.symm
```

*Mathematical Significance:* For a local ring $R$, the stalk of $\mathrm{Spec}(R)$ at the closed point (corresponding to the maximal ideal) is naturally isomorphic to $R$ itself. This isomorphism captures the fact that localizing a local ring at its maximal ideal gives back the original ring.

This result provides the foundation for understanding how stalks behave in the local case and establishes the connection between abstract stalk theory and concrete local rings.

== Spec and FromSpecStalk

```lean
lemma Spec_stalkClosedPointIso :
    Spec.map (stalkClosedPointIso R).inv = (Spec R).fromSpecStalk (closedPoint R) := by
  rw [stalkClosedPointIso_inv, Scheme.Spec_fromSpecStalk']
```

*Mathematical Significance:* The canonical isomorphism between the stalk and the original ring induces a morphism that coincides with the fromSpecStalk construction. This provides a concrete computational handle on the abstract fromSpecStalk morphism in the case of spectra of local rings.

= Local Homomorphisms and Morphisms

== Stalk Maps from Morphisms

```lean
noncomputable
def stalkClosedPointTo :
    X.presheaf.stalk (f.base (closedPoint R)) ⟶ R :=
  f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom
```

*Mathematical Significance:* Given a morphism $f: \mathrm{Spec}(R) \to X$ where $R$ is a local ring, we obtain a canonical ring homomorphism from the stalk of $X$ at $f(\mathfrak{m})$ (where $\mathfrak{m}$ is the closed point of $\mathrm{Spec}(R)$) to $R$.

This construction is fundamental for understanding how morphisms from spectra of local rings encode local ring homomorphisms.

== Local Homomorphism Property

```lean
instance isLocalHom_stalkClosedPointTo :
    IsLocalHom (stalkClosedPointTo f).hom :=
  inferInstanceAs <| IsLocalHom (f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom).hom
\end{LST}

\textbf{Mathematical Significance:} The ring homomorphism obtained from a morphism to a spectrum of a local ring is automatically a local homomorphism (i.e., it maps the maximal ideal to the maximal ideal). This reflects the geometric fact that morphisms to spectra of local rings naturally encode local algebraic data.

= Universal Property


== Equivalence with Local Ring Homomorphisms


```lean
@[simps]
noncomputable
def SpecToEquivOfLocalRing :
    (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom } where
  toFun f := ⟨f.base (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
```

*Mathematical Significance:* This establishes a fundamental bijection between:
\item Morphisms from $\mathrm{Spec*(R)$ (where $R$ is a local ring) to a scheme $X$
\item Pairs $(x, \phi)$ where $x$ is a point of $X$ and $\phi: \mathcal{O*_{X,x} \to R$ is a local ring homomorphism

This universal property is one of the most important results in scheme theory, as it shows that morphisms from spectra of local rings correspond exactly to pointed local ring homomorphisms. It provides the algebraic foundation for understanding how "geometric points with values in local rings" work in scheme theory.

= Geometric Significance

== Local-Global Principle

The stalk theory developed in this file establishes several crucial local-global principles:

\item *Local Detection of Properties*: Many properties of morphisms and schemes can be detected by examining their behavior on stalks
\item *Localization Principle*: Global problems can often be reduced to local problems by passing to stalks
\item *Functorial Behavior*: All constructions respect morphisms and maintain the relationships between different parts of the geometry

== Connection to Classical Algebraic Geometry

The stalk construction provides the bridge between modern scheme theory and classical algebraic geometry:

\item *Local Rings*: Stalks generalize the notion of local rings of functions at points on varieties
\item *Localization*: The construction matches classical localization of coordinate rings at prime ideals
\item *Specialization*: The range characterization captures the classical notion of how points can degenerate to others

== Applications

The stalk theory has numerous applications throughout algebraic geometry:

\item *Dimension Theory*: Local dimensions can be computed using stalks
\item *Smoothness and Singularities*: Smooth and singular points can be detected through stalk properties
\item *Coherent Sheaves*: The theory of coherent sheaves relies heavily on stalk computations
\item *Étale and Flat Morphisms*: Many important classes of morphisms are characterized by their behavior on stalks
\item *Base Change*: Stalks behave predictably under base change operations

The stalk construction thus provides both the theoretical foundation and practical tools needed for much of modern algebraic geometry, making it one of the most important technical developments in the field.
