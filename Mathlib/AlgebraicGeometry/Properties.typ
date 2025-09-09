#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Properties.lean* file in Mathlib4. The file establishes fundamental properties that schemes can satisfy, focusing on two crucial notions from classical algebraic geometry: reduced and integral schemes. These properties form the foundation for understanding the geometric behavior of schemes and their relationship to classical algebraic varieties.

= Topological Properties of Schemes

== T₀ Spaces

```lean
instance : T0Space X :=
  T0Space.of_open_cover fun x => ⟨_, X.affineCover.covers x,
    (X.affineCover.map x).opensRange.2, IsEmbedding.t0Space (Y := PrimeSpectrum _)
    (isAffineOpen_opensRange (X.affineCover.map x)).isoSpec.schemeIsoToHomeo.isEmbedding⟩
```

*Mathematical Significance:* Every scheme is a T₀ topological space. This means that for any two distinct points, there exists an open set containing one but not the other. This property is fundamental to the geometric nature of schemes and ensures that the topological structure carries meaningful geometric information.

== Quasi-Sober Spaces

```lean
instance : QuasiSober X := by
  apply (config := { allowSynthFailures := true })
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.map x).base)
```

*Mathematical Significance:* Every scheme is quasi-sober, meaning that every irreducible closed subset has a unique generic point. This property connects the topological structure of schemes to their algebraic nature, ensuring that irreducible components correspond to prime ideals in a natural way.

== Prespectral Spaces

```lean
instance {X : Scheme.{u}} : PrespectralSpace X :=
  have (Y : Scheme.{u}) (_ : IsAffine Y) : PrespectralSpace Y :=
    .of_isClosedEmbedding (Y := PrimeSpectrum _) _
      Y.isoSpec.hom.homeomorph.isClosedEmbedding
  have (i : _) : PrespectralSpace (X.affineCover.map i).opensRange.1 :=
    this (X.affineCover.map i).opensRange (isAffineOpen_opensRange (X.affineCover.map i))
  .of_isOpenCover X.affineCover.isOpenCover_opensRange
```

*Mathematical Significance:* Every scheme is a prespectral space, which means it satisfies certain separation and compactness properties that are weaker than being spectral but still ensure good geometric behavior. This property is inherited from affine schemes being spectra of rings.

= Reduced Schemes

== Definition of Reduced Schemes

```lean
class IsReduced : Prop where
  component_reduced : ∀ U, _root_.IsReduced Γ(X, U) := by infer_instance
```

*Mathematical Significance:* A scheme $X$ is reduced if all sections of its structure sheaf over any open set form a reduced ring (i.e., have no nonzero nilpotent elements). Geometrically, this means the scheme has no "infinitesimal thickening" - it corresponds to a classical algebraic variety without embedded points or multiple components.

In classical algebraic geometry, reduced schemes correspond to radical ideals. The condition ensures that the scheme captures only the "geometric" information without any scheme-theoretic multiplicities.

== Characterization via Stalks

```lean
theorem isReduced_of_isReduced_stalk [∀ x : X, _root_.IsReduced (X.presheaf.stalk x)] :
    IsReduced X := by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [RingHom.map_zero]
  change X.presheaf.germ U x hx s = 0
  exact (hs.map _).eq_zero
```

*Mathematical Significance:* A scheme is reduced if and only if all its stalks are reduced. This provides a local characterization of the reduced property, showing that the global geometric property can be verified by checking local algebraic conditions at each point.

== Reduced Property and Basic Opens

```lean
@[simp]
theorem basicOpen_eq_bot_iff {X : Scheme} [IsReduced X] {U : X.Opens}
    (s : Γ(X, U)) : X.basicOpen s = ⊥ ↔ s = 0 := by
  refine ⟨eq_zero_of_basicOpen_eq_bot s, ?_⟩
  rintro rfl
  simp
```

*Mathematical Significance:* In a reduced scheme, a section has empty basic open (meaning it vanishes everywhere) if and only if the section is zero. This captures the geometric intuition that in reduced schemes, a function that vanishes at all points must be the zero function - there are no "nilpotent directions" where a nonzero function can still have empty zero set.

= Integral Schemes

== Definition of Integral Schemes

```lean
class IsIntegral : Prop where
  nonempty : Nonempty X := by infer_instance
  component_integral : ∀ (U : X.Opens) [Nonempty U], IsDomain Γ(X, U) := by infer_instance
```

*Mathematical Significance:* A scheme $X$ is integral if it is nonempty and the ring of sections over any nonempty open set is an integral domain. This is the scheme-theoretic generalization of irreducible algebraic varieties - integral schemes correspond to geometric objects that cannot be decomposed as a union of proper closed subvarieties.

Integral schemes are fundamental in algebraic geometry as they correspond to:
\item Irreducible algebraic varieties in classical geometry
\item Geometric objects with a well-defined function field
\item Schemes whose coordinate rings are integral domains

== Relationship Between Integral and Reduced

```lean
instance (priority := 900) isReduced_of_isIntegral [IsIntegral X] : IsReduced X := by
  constructor
  intro U
  rcases U.1.eq_empty_or_nonempty with h | h
  · have : U = ⊥ := SetLike.ext' h
    haveI : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty this)
    infer_instance
  · haveI : Nonempty U := by simpa
    infer_instance
```

*Mathematical Significance:* Every integral scheme is automatically reduced. This reflects the algebraic fact that integral domains have no nilpotent elements. Geometrically, irreducible varieties cannot have embedded components or multiplicities.

== Integral Schemes and Irreducible Spaces

```lean
instance irreducibleSpace_of_isIntegral [IsIntegral X] : IrreducibleSpace X := by
  by_contra H
  replace H : ¬IsPreirreducible (⊤ : Set X) := fun h =>
    H { toPreirreducible := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  -- The proof continues by showing this leads to a contradiction
```

*Mathematical Significance:* Every integral scheme has an irreducible underlying topological space. This establishes the fundamental connection between the algebraic property (integral domains) and the topological property (irreducibility).

== Equivalence Characterization

```lean
theorem isIntegral_iff_irreducibleSpace_and_isReduced :
    IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegral_of_irreducibleSpace_of_isReduced X⟩
```

*Mathematical Significance:* A scheme is integral if and only if it is both irreducible as a topological space and reduced. This provides a clean geometric characterization: integral schemes are exactly the reduced irreducible schemes.

This equivalence bridges algebraic and geometric viewpoints:
\item Algebraic: Sections form integral domains
\item Geometric: The space is irreducible and has no embedded components

= Preservation Properties

== Preservation Under Open Immersions

```lean
theorem isReduced_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsReduced Y] : IsReduced X := by
  constructor
  intro U
  have : U = f ^{-1}U f ^U U := by
    ext1; exact (Set.preimage_image_eq _ H.base_open.injective).symm
  rw [this]
  exact isReduced_of_injective (inv <| f.app (f ^U U)).hom
    (asIso <| f.app (f ^U U) : Γ(Y, f ^U U) ≅ _).symm.commRingCatIsoToRingEquiv.injective
```

*Mathematical Significance:* The reduced property is preserved under open immersions. This means that open subschemes of reduced schemes are reduced, reflecting the local nature of the reduced condition.

== Preservation for Integral Schemes

```lean
theorem isIntegral_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [IsIntegral Y] [Nonempty X] : IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  have : U = f ^{-1}U f ^U U := by ext1; exact (Set.preimage_image_eq _ H.base_open.injective).symm
  rw [this]
  have : IsDomain Γ(Y, f ^U U) := by
    apply (config := { allowSynthFailures := true }) IsIntegral.component_integral
    exact ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.app (f ^U U) :
    Γ(Y, f ^U U) ≅ _).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
```

*Mathematical Significance:* Nonempty open subschemes of integral schemes are integral. This shows that integrality is preserved under "geometric inclusions" that don't introduce new irreducible components.

= Affine Case

== Characterization for Affine Schemes

```lean
theorem affine_isReduced_iff (R : CommRingCat) :
    IsReduced (Spec R) ↔ _root_.IsReduced R := by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  exact isReduced_of_injective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective
```

*Mathematical Significance:* For affine schemes, the scheme is reduced if and only if the corresponding ring is reduced. This establishes the fundamental dictionary between algebraic properties of rings and geometric properties of their spectra.

```lean
theorem affine_isIntegral_iff (R : CommRingCat) :
    IsIntegral (Spec R) ↔ IsDomain R :=
  ⟨fun _ => MulEquiv.isDomain Γ(Spec R, ⊤)
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩
```

*Mathematical Significance:* For affine schemes, the scheme is integral if and only if the corresponding ring is an integral domain. This provides the direct translation between algebraic geometry and commutative algebra for the most basic geometric objects.

= Geometric Significance

The properties defined in this file capture fundamental geometric concepts:

\item *Reduced schemes* correspond to classical algebraic varieties without embedded points or nilpotent structure. They represent the "honest" geometric objects where functions that vanish everywhere are actually zero.

\item *Integral schemes* are the irreducible geometric objects - they cannot be written as a union of proper closed subvarieties. These are the building blocks of algebraic geometry, analogous to irreducible varieties in classical algebraic geometry.

\item The relationship $\text{Integral* \Rightarrow \text{Reduced}$ reflects the fundamental fact that irreducible objects cannot have embedded components.

\item The characterization $\text{Integral* \Leftrightarrow \text{Irreducible} \cap \text{Reduced}$ provides a clean geometric understanding of integrality.

These properties form the foundation for more advanced concepts in scheme theory and are essential for understanding the geometric behavior of algebraic objects defined by polynomial equations.
