#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `FunctionField.lean* file in Mathlib4. The file develops the theory of function fields for integral schemes, which is one of the most fundamental concepts in algebraic geometry. The function field captures the "generic" behavior of rational functions on an irreducible variety and serves as the algebraic counterpart to the geometric notion of the generic point.

In classical algebraic geometry, the function field of an irreducible variety is the field of rational functions on that variety. In scheme theory, this becomes the stalk of the structure sheaf at the generic point of an irreducible scheme. This generalization provides a powerful tool for understanding the global properties of schemes through local algebraic data.

= The Function Field

== Definition

```lean
noncomputable abbrev Scheme.functionField [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)
```

*Mathematical Significance:* The function field of an irreducible scheme $X$ is defined as the stalk of the structure sheaf at the generic point of $X$. Despite the name, this is only a field when the scheme is integral (both irreducible and reduced).

The generic point represents the "most general" point of the scheme - it specializes to every other point. Therefore, the stalk at the generic point captures the most general algebraic behavior of the scheme and contains the minimal amount of algebraic information needed to understand the entire scheme.

In classical terms, if $X = \mathrm{Spec*(R)$ where $R$ is an integral domain, then the function field is the field of fractions of $R$, which consists of all formal quotients $\frac{f}{g}$ where $f, g \in R$ and $g \neq 0$.

== Canonical Germ Maps

```lean
noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X] (U : X.Opens)
    [h : Nonempty U] : Γ(X, U) ⟶ X.functionField :=
  X.presheaf.germ U
    (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h))
```

*Mathematical Significance:* For any nonempty open subset $U$ of an irreducible scheme $X$, there is a canonical ring homomorphism from the sections over $U$ to the function field. This map sends each section to its "germ" or "value" at the generic point.

This construction establishes the function field as the "limit" of all the section rings as we take smaller and smaller (but still nonempty) open sets. Since the generic point lies in every nonempty open set of an irreducible scheme, we always have such a canonical map.

= Field Structure for Integral Schemes

== Field Instance

```lean
noncomputable instance [IsIntegral X] : Field X.functionField := by
  refine .ofIsUnitOrEqZero fun a ↦ ?_
  obtain ⟨U, m, s, rfl⟩ := TopCat.Presheaf.germ_exist _ _ a
  rw [or_iff_not_imp_right, ← (X.presheaf.germ _ _ m).hom.map_zero]
  intro ha
  replace ha := ne_of_apply_ne _ ha
  have hs : genericPoint X ∈ RingedSpace.basicOpen _ s := by
    rw [← SetLike.mem_coe, (genericPoint_spec X).mem_open_set_iff,
      Set.univ_inter, Set.nonempty_iff_ne_empty, Ne, ← Opens.coe_bot, ← SetLike.ext'_iff]
    · erw [basicOpen_eq_bot_iff]
      exact ha
    · exact (RingedSpace.basicOpen _ _).isOpen
  have := (X.presheaf.germ _ _ hs).hom.isUnit_map (RingedSpace.isUnit_res_basicOpen _ s)
  rwa [Presheaf.germ_res_apply] at this
```

*Mathematical Significance:* When the scheme is integral (irreducible and reduced), the function field is indeed a field. The proof shows that every nonzero element has an inverse by using the fundamental property that in integral schemes, a section that doesn't vanish identically must be invertible on some basic open set, and since the generic point lies in every nonempty open, it lies in this basic open where the section is invertible.

This result establishes the crucial connection between the geometric notion of integrality and the algebraic notion of being a field. It shows that integral schemes have well-defined function fields that capture their rational function behavior.

= Injectivity Properties

== Germ Injectivity

```lean
theorem germ_injective_of_isIntegral [IsIntegral X] {U : X.Opens} (x : X) (hx : x ∈ U) :
    Function.Injective (X.presheaf.germ U x hx) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ U x hx).hom.map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ hx hx _ _ hy
  cases Subsingleton.elim iU iV
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e
```

*Mathematical Significance:* In an integral scheme, the germ map from any open set to any stalk is injective. This fundamental result shows that in integral schemes, sections can be uniquely recovered from their germs, reflecting the fact that integral domains embed into their fields of fractions.

== Function Field Map Injectivity

```lean
theorem Scheme.germToFunctionField_injective [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_isIntegral _ _ _
```

*Mathematical Significance:* The canonical map from sections over any nonempty open set to the function field is injective for integral schemes. This means that the function field contains a faithful copy of all the section rings, making it a universal repository for the rational functions on the scheme.

= Behavior Under Morphisms

== Generic Points and Open Immersions

```lean
theorem genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [hX : IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert (genericPoint_spec X).image (show Continuous f.base by fun_prop)
  symm
  rw [← Set.univ_subset_iff]
  convert subset_closure_inter_of_isPreirreducible_of_isOpen _ H.base_open.isOpen_range _
```

*Mathematical Significance:* When we have an open immersion between irreducible schemes, the generic point of the source maps to the generic point of the target. This fundamental result ensures that open subschemes of irreducible schemes have the "same" generic point, preserving the function field structure.

This property is crucial for understanding how function fields behave under geometric inclusions and ensures that rational functions on a scheme can be naturally extended to any larger scheme containing it as an open subscheme.

= Affine Case

== Generic Point in Spectra

```lean
@[simp]
theorem genericPoint_eq_bot_of_affine (R : CommRingCat) [IsDomain R] :
    genericPoint (Spec R) = (⊥ : PrimeSpectrum R) := by
  apply (genericPoint_spec (Spec R)).eq
  rw [isGenericPoint_def]
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
  rw [← PrimeSpectrum.zeroLocus_singleton_zero]
  rfl
```

*Mathematical Significance:* For the spectrum of an integral domain $R$, the generic point is the zero ideal $(0)$, which corresponds to the smallest prime ideal. This makes algebraic sense because the zero ideal represents the "most general" prime, and localizing at it gives the field of fractions.

== Fraction Ring Structure

```lean
instance functionField_isFractionRing_of_affine (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Spec R).functionField := by
  convert StructureSheaf.IsLocalization.to_stalk R (genericPoint (Spec R))
  delta IsFractionRing IsLocalization.AtPrime
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero
```

*Mathematical Significance:* For an affine integral scheme $\mathrm{Spec}(R)$ where $R$ is an integral domain, the function field is precisely the field of fractions of $R$. This establishes the fundamental dictionary between algebraic and geometric notions of function fields.

This result connects the abstract scheme-theoretic definition with the classical algebraic notion, showing that our geometric construction recovers the familiar algebraic object in the affine case.

= Local Properties

== Fraction Ring Property for Affine Opens

```lean
theorem functionField_isFractionRing_of_isAffineOpen [IsIntegral X] (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  haveI : IsAffine _ := hU
  haveI : IsIntegral U :=
    @isIntegral_of_isAffine_of_isDomain _ _ _
      (by rw [Scheme.Opens.toScheme_presheaf_obj, Opens.isOpenEmbedding_obj_top]; infer_instance)
  delta IsFractionRing Scheme.functionField
  convert hU.isLocalization_stalk ⟨genericPoint X,
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))⟩ using 1
```

*Mathematical Significance:* For any nonempty affine open subset $U$ of an integral scheme $X$, the function field of $X$ is the field of fractions of $\Gamma(X, U)$. This shows that the function field can be constructed from the sections over any sufficiently large affine open set.

This result provides a practical way to compute function fields and shows that they have a local nature - they can be understood by examining sufficiently large affine pieces of the scheme.

== Stalk-Function Field Relationship

```lean
instance [IsIntegral X] (x : X) :
    IsFractionRing (X.presheaf.stalk x) X.functionField :=
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  let x : U := ⟨x, X.affineCover.covers x⟩
  have : Nonempty U := ⟨x⟩
  -- Technical proof involving localizations
```

*Mathematical Significance:* For any point $x$ in an integral scheme $X$, the function field is the field of fractions of the stalk at $x$. This establishes a fundamental relationship between local and global properties of integral schemes.

This result shows that every stalk naturally embeds into the function field, and the function field can be constructed as the field of fractions of any stalk. This provides multiple equivalent ways to think about and construct function fields.

= Domain Properties

== Stalks as Integral Domains

```lean
instance [IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) (X.functionField))
```

*Mathematical Significance:* In an integral scheme, every stalk is an integral domain. This follows from the fact that each stalk embeds into the function field (which is a field), and subrings of fields are integral domains.

This result provides a local characterization of integrality and shows that the global geometric property of being integral translates directly to local algebraic properties at every point.

= Geometric Significance

The function field theory developed in this file captures several fundamental aspects of algebraic geometry:

\item *Rational Functions*: The function field provides the scheme-theoretic generalization of the field of rational functions on an algebraic variety. It captures the "generic" algebraic behavior of the scheme.

\item *Generic Point Philosophy*: By defining the function field as the stalk at the generic point, the theory makes precise the intuitive idea that generic behavior determines specific behavior in algebraic geometry.

\item *Local-Global Principle*: The various characterizations (via affine opens, stalks, etc.) show that global function fields can be understood through local algebraic data.

\item *Birational Invariance*: The function field captures the birational geometry of schemes - schemes that are birationally equivalent have isomorphic function fields.

\item *Integrality Detection*: The field property of function fields provides a way to detect and characterize integral schemes through their most generic algebraic data.

The function field serves as a bridge between the geometric intuition of "rational functions defined everywhere except on lower-dimensional sets" and the algebraic precision required for modern algebraic geometry. It provides the foundation for many advanced topics including birational geometry, function field arithmetic, and the study of rational points on schemes.
