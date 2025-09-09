#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Noetherian.lean* file in Mathlib4. The file develops the theory of Noetherian schemes, which are fundamental objects in algebraic geometry that exhibit finite generation properties. Noetherian schemes generalize the classical concept of Noetherian varieties and are essential for many foundational results in scheme theory, including the existence of finite stratifications and the finiteness of various geometric invariants.

The Noetherian property captures the idea that algebraic objects defined by finitely many equations should satisfy various finiteness conditions, making them amenable to computational and theoretical analysis.

= Locally Noetherian Schemes

== Definition

```lean
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : ∀ (U : X.affineOpens),
    IsNoetherianRing Γ(X, U) := by infer_instance
```

*Mathematical Significance:* A scheme $X$ is locally Noetherian if the ring of sections over every affine open subset is a Noetherian ring. This condition ensures that locally, the scheme behaves like the spectrum of a Noetherian ring, which has many desirable finiteness properties.

In classical algebraic geometry, this corresponds to varieties that can be covered by open sets each isomorphic to closed subvarieties of affine space defined by finitely many polynomial equations, where the coordinate rings satisfy the ascending chain condition on ideals.

== Key Localization Lemma

```lean
theorem isNoetherianRing_of_away : IsNoetherianRing R := by
  apply monotone_stabilizes_iff_noetherian.mp
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : ℕ | ∀ m : ℕ, n ≤ m → (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
```

*Mathematical Significance:* This is the key technical lemma establishing that if $R$ is a ring and $\{f_i\}$ is a finite collection of elements generating the unit ideal, then $R$ is Noetherian if and only if each localization $R_{f_i}$ is Noetherian. This result is fundamental to the local-global principle for the Noetherian property.

The proof follows Hartshorne's approach and is crucial for showing that local Noetherian conditions can be globalized to the entire scheme.

== Characterization via Covers

```lean
theorem isLocallyNoetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X)
    [∀ i, IsAffine (𝒰.obj i)] :
    IsLocallyNoetherian X ↔ ∀ (i : 𝒰.J), IsNoetherianRing Γ(𝒰.obj i, ⊤) := by
```

*Mathematical Significance:* A scheme is locally Noetherian if and only if it admits an affine open cover where each component has Noetherian ring of global sections. This provides a practical criterion for verifying the locally Noetherian property and shows that it can be checked on any affine cover.

This characterization is essential because it allows us to verify Noetherian properties by examining a finite amount of algebraic data (the rings of sections over the cover components).

= Geometric Consequences

== Quasi-Compactness of Open Immersions

```lean
@[stacks 01OX]
instance (priority := 100) {Z : Scheme} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [IsOpenImmersion f] : QuasiCompact f := by
  apply (quasiCompact_iff_forall_affine f).mpr
  intro U hU
  rw [Opens.map_coe, ← Set.preimage_inter_range]
  apply f.isOpenEmbedding.isInducing.isCompact_preimage'
```

*Mathematical Significance:* Any open immersion into a locally Noetherian scheme is quasi-compact. This is a fundamental result showing that Noetherian conditions impose strong compactness constraints on the geometry.

Geometrically, this means that any open subset of a locally Noetherian scheme, when viewed as a scheme itself, has the property that its morphisms to other schemes have compact fibers over affine open sets.

== Quasi-Separated Property

```lean
@[stacks 01OY]
instance (priority := 100) IsLocallyNoetherian.quasiSeparatedSpace [IsLocallyNoetherian X] :
    QuasiSeparatedSpace X := by
  apply (quasiSeparatedSpace_iff_affine X).mpr
  intro U V
  have hInd := U.2.fromSpec.isOpenEmbedding.isInducing
  apply (hInd.isCompact_preimage_iff ?_).mp
```

*Mathematical Significance:* Every locally Noetherian scheme is quasi-separated, meaning that the intersection of any two affine open sets is quasi-compact. This separation property is crucial for many geometric constructions and ensures that the scheme has well-behaved intersection properties.

This result establishes that Noetherian conditions automatically provide good separation properties, which are essential for defining and working with various scheme-theoretic constructions like proper morphisms and coherent sheaves.

= Noetherian Schemes

== Definition

```lean
@[mk_iff]
class IsNoetherian (X : Scheme) : Prop extends IsLocallyNoetherian X, CompactSpace X
```

*Mathematical Significance:* A scheme is Noetherian if it is both locally Noetherian and quasi-compact as a topological space. This combines the local finiteness condition with a global compactness requirement, ensuring that the scheme can be covered by finitely many affine Noetherian opens.

Noetherian schemes are the scheme-theoretic generalization of affine varieties over Noetherian rings and inherit many of their good finiteness properties.

== Finite Cover Characterization

```lean
theorem isNoetherian_iff_of_finite_affine_openCover {𝒰 : Scheme.OpenCover.{v, u} X}
    [Finite 𝒰.J] [∀ i, IsAffine (𝒰.obj i)] :
    IsNoetherian X ↔ ∀ (i : 𝒰.J), IsNoetherianRing Γ(𝒰.obj i, ⊤) := by
```

*Mathematical Significance:* A scheme is Noetherian if and only if it admits a finite affine open cover where each component has Noetherian ring of global sections. This provides the most practical criterion for recognizing Noetherian schemes.

This characterization shows that Noetherian schemes are exactly those that can be constructed by gluing finitely many spectra of Noetherian rings, making them very concrete and computable objects.

== Topological Noetherian Property

```lean
@[stacks 01OZ]
instance (priority := 100) IsNoetherian.noetherianSpace [IsNoetherian X] :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  let 𝒰 := X.affineCover.finiteSubcover
  rw [← 𝒰.iUnion_range]
  suffices ∀ i : 𝒰.J, NoetherianSpace (Set.range <| (𝒰.map i).base) by
    apply NoetherianSpace.iUnion
```

*Mathematical Significance:* Every Noetherian scheme has a Noetherian underlying topological space. This means that every descending chain of closed subsets eventually stabilizes, providing strong finiteness conditions on the closed subvarieties of the scheme.

This topological Noetherian property is fundamental for many applications, including the existence of finite stratifications and the finiteness of irreducible components.

= Affine Case

== Correspondence with Noetherian Rings

```lean
instance {R : CommRingCat} [IsNoetherianRing R] :
    IsLocallyNoetherian (Spec R) := by
  apply isLocallyNoetherian_of_affine_cover
    (ι := Fin 1) (S := fun _ => ⟨⊤, isAffineOpen_top (Spec R)⟩)
  · exact iSup_const
  · intro
    apply isNoetherianRing_of_ringEquiv R
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (Scheme.ΓSpecIso R).symm
```

*Mathematical Significance:* If $R$ is a Noetherian ring, then $\mathrm{Spec}(R)$ is a Noetherian scheme. This establishes the fundamental dictionary between Noetherian rings and Noetherian schemes in the affine case.

```lean
theorem isNoetherian_Spec {R : CommRingCat} :
    IsNoetherian (Spec R) ↔ IsNoetherianRing R :=
  ⟨fun _ => inferInstance,
   fun _ => inferInstance⟩
```

*Mathematical Significance:* For affine schemes, being Noetherian is equivalent to the corresponding ring being Noetherian. This provides the direct translation between the geometric and algebraic Noetherian conditions.

= Stalks and Local Properties

== Noetherian Stalks

```lean
instance [IsLocallyNoetherian X] {x : X} : IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by aesop)
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hU ⟨x, hU2⟩
  exact @IsLocalization.isNoetherianRing _ _ (hU.primeIdealOf ⟨x, hU2⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hU2⟩)
        this (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)
```

*Mathematical Significance:* In a locally Noetherian scheme, every stalk is a Noetherian ring. This provides the local algebraic foundation for the Noetherian property and shows that the geometric condition translates to strong algebraic finiteness properties at every point.

The Noetherian property of stalks is crucial for many local-to-global arguments in algebraic geometry and ensures that various module-theoretic constructions behave well.

= Finite Irreducible Components

== Finiteness Result

```lean
@[stacks 0BA8]
theorem finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
```

*Mathematical Significance:* A Noetherian scheme has only finitely many irreducible components. This is one of the most important consequences of the Noetherian property, providing a fundamental finiteness result for the geometric decomposition of schemes.

This finiteness is essential for many applications:
\item It allows for finite inductive arguments on the components
\item It ensures that various invariants (like dimension) are well-defined
\item It provides the foundation for intersection theory and numerical invariants

= Global Geometric Significance

The Noetherian property for schemes captures several fundamental finiteness concepts from classical algebraic geometry:

\item *Finite Generation*: The coordinate rings are finitely generated over their base rings, ensuring computational tractability.

\item *Ascending Chain Condition*: Every chain of ideals (corresponding to descending chains of closed subschemes) eventually stabilizes, providing strong structural constraints.

\item *Finite Decomposition*: The scheme has finitely many irreducible components, allowing for finite inductive arguments and well-defined numerical invariants.

\item *Quasi-Compactness*: The scheme can be covered by finitely many affine opens, making it amenable to algebraic analysis.

\item *Coherence Properties*: Many sheaf-theoretic constructions (like coherent sheaves) behave well on Noetherian schemes, providing the foundation for advanced algebraic geometry.

The theory developed in this file shows that these classical finiteness properties can be systematically generalized to the scheme-theoretic setting, preserving their essential geometric content while extending their applicability to more general algebraic objects.

Noetherian schemes form the natural setting for much of modern algebraic geometry, as they retain the computational and theoretical tractability of classical varieties while allowing for the additional flexibility provided by scheme theory.
