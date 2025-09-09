#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `GammaSpecAdjunction.lean* file in Mathlib4. The file establishes the fundamental adjunction between the global sections functor $\Gamma$ and the spectrum functor $\mathrm{Spec}$, which is one of the cornerstones of algebraic geometry.

The adjunction $\Gamma \dashv \mathrm{Spec*$ captures the duality between geometry and algebra: geometric objects (locally ringed spaces/schemes) correspond to algebraic objects (commutative rings) via this adjunction. This relationship is at the heart of the philosophy that "geometry is dual to algebra."

= Mathematical Background

The adjunction establishes that for any locally ringed space $X$ and commutative ring $R$:
$$\text{Hom*(X, \mathrm{Spec}(R)) \cong \text{Hom}(R, \Gamma(X, \mathcal{O}_X))$$

This means that morphisms from a locally ringed space to an affine scheme are in natural bijection with ring homomorphisms from the ring to the global sections of the space.

Since we're working with contravariant functors, the adjunction is technically between $\Gamma^{\text{op*}$ and $\mathrm{Spec}$, or equivalently $\mathrm{Spec}^{\text{op}} \dashv \Gamma$.

= The Unit: Canonical Map to Spec of Global Sections

== Construction of the Underlying Map

```lean
def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  PrimeSpectrum.map (LocallyRingedSpace.Γ.map X.toΓSpec.c.app (op ⊤)) x.1
```

*Natural Language:* For any locally ringed space $X$, we construct a continuous map from $X$ to $\mathrm{Spec}(\Gamma(X, \mathcal{O}_X))$. Each point $x \in X$ maps to the prime ideal that is the kernel of the composition of the stalk map $\Gamma(X, \mathcal{O}_X) \to \mathcal{O}_{X,x}$ with the natural map to the residue field.

== Relationship with Stalks and Units

```lean
theorem notMem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ X.toΓSpecFun x ↔ IsUnit (X.presheaf.germ (⟨x, trivial⟩ : X.basicOpen r) r)
```

*Natural Language:* A global section $r$ is not in the prime ideal corresponding to point $x$ if and only if $r$ becomes a unit in the stalk at $x$. This captures the fundamental relationship between the algebraic (prime ideal) and geometric (stalk) perspectives.

== Basic Opens and Preimages

```lean
theorem toΓSpec_preimage_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' PrimeSpectrum.basicOpen r = X.basicOpen r
```

*Natural Language:* The preimage of a basic open set $D(r)$ in $\mathrm{Spec}(\Gamma(X, \mathcal{O}_X))$ under the canonical map is exactly the basic open set $D(r)$ in $X$. This shows that the map respects the basic open sets, which are fundamental to the topology.

== Continuity

```lean
theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  rw [continuous_iff_isClosed]
  intro S hS
  rw [PrimeSpectrum.isClosed_zeroLocus_iff] at hS
  obtain ⟨T, rfl⟩ := hS
  simp only [toΓSpecFun, Set.preimage_setOf_eq, PrimeSpectrum.mem_zeroLocus]
  rw [X.toΓSpec_preimage_zeroLocus_eq T]
  exact X.zeroLocus_isClosed T
```

*Natural Language:* The canonical map $X \to \mathrm{Spec}(\Gamma(X, \mathcal{O}_X))$ is continuous. This is shown by proving that preimages of closed sets (zero loci) are closed.

= Sheaf Morphism Construction

== Component Apps on Basic Opens

```lean
def toΓSpecCApp :
    (structureSheaf (Γ.obj (op X))).1.obj (op (basicOpen r)) ⟶
    X.presheaf.obj (op (X.basicOpen r)) :=
  -- Complex construction involving localizations and restrictions
```

*Natural Language:* For each basic open $D(r)$ in $\mathrm{Spec}(\Gamma(X, \mathcal{O}_X))$, we need to construct compatible maps from the structure sheaf to the pullback of $X$'s presheaf. This involves carefully handling localizations and the relationship between basic opens.

== Compatibility Conditions

```lean
theorem toΓSpecCApp_spec : toOpen _ (basicOpen r) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
```

*Natural Language:* The constructed sheaf maps are compatible with the natural inclusions of ring elements into localizations. This ensures that our construction respects the ring structure.

= The Complete Unit Morphism

== As a Morphism of Locally Ringed Spaces

```lean
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) where
  -- Underlying continuous map
  base := X.toΓSpecBase
  -- Sheaf morphism
  c := X.toΓSpecSheafedSpace.c
  -- Proof that stalk maps are local ring homomorphisms
  isLocalAtTarget := -- proof
```

*Natural Language:* The complete unit morphism $X \to \mathrm{Spec}(\Gamma(X, \mathcal{O}_X))$ consists of the continuous map we constructed plus a compatible sheaf morphism. The additional requirement is that the induced stalk maps are local ring homomorphisms.

== Stalk Map Properties

```lean
theorem toStalk_stalkMap_toΓSpec (x : X) :
    toStalk _ (X.toΓSpecFun x) ≫ X.toΓSpec.stalkMap x = X.presheaf.germ ⟨x, trivial⟩
```

*Natural Language:* The stalk maps induced by the unit morphism are compatible with the natural germ maps. This ensures that local information is preserved under the unit morphism.

= Compatibility with Zero Loci

```lean
lemma toΓSpec_preimage_zeroLocus_eq {X : LocallyRingedSpace.{u}}
    (S : Set (Γ.obj (op X))) :
    X.toΓSpecFun ⁻¹' PrimeSpectrum.zeroLocus S = X.zeroLocus S
```

*Natural Language:* The unit morphism preserves zero loci: the preimage of $V(S)$ in $\mathrm{Spec}(\Gamma(X, \mathcal{O}_X))$ is exactly $V(S)$ in $X$. This is a crucial compatibility that ensures the morphism respects the closed subspace structure.

= Triangle Identities

== Left Triangle ($\Gamma$-Spec-$\Gamma$ Identity)

```lean
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _ := by
  rw [← toOpen_comp_toΓSpecCApp]
  exact toΓSpecCApp_spec _ (Set.mem_univ _) ⟨⊤, le_rfl⟩
```

*Natural Language:* One of the triangle identities for the adjunction: composing the natural isomorphism $R \cong \Gamma(\mathrm{Spec}(R), \mathcal{O})$ with the unit at $\mathrm{Spec}(R)$ gives the identity. This expresses that "Spec undoes Gamma" on affine objects.

== Right Triangle (Spec-$\Gamma$-Spec Identity)

```lean
theorem right_triangle (R : CommRingCat) :
    Spec.locallyRingedSpaceObj R.toΓSpec ≫
    LocallyRingedSpace.SpecΓIdentity.hom.app R = 𝟙 _
```

*Natural Language:* The other triangle identity: composing the unit at a ring $R$ with the counit gives the identity on $R$. This expresses that "Gamma undoes Spec" on rings.

= The Adjunctions

== Locally Ringed Space Level

```lean
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} where
  unit := identityToΓSpec
  counit := LocallyRingedSpace.SpecΓIdentity.inv
  left_triangle := left_triangle
  right_triangle := right_triangle
```

*Natural Language:* The adjunction between $\Gamma^{\text{op}}$ and $\mathrm{Spec}$ at the level of locally ringed spaces. The unit is the canonical map we constructed, and the counit is the natural isomorphism between rings and global sections of their spectra.

== Scheme Level

```lean
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where
  unit :=
  { app := fun X ↦ ⟨locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace⟩
    naturality := fun X Y f =>
      Scheme.Hom.ext' (locallyRingedSpaceAdjunction.{u}.unit.naturality f.toLRSHom) }
  counit := locallyRingedSpaceAdjunction.counit
  left_triangle := -- lifting of locally ringed space triangle
  right_triangle := -- lifting of locally ringed space triangle
```

*Natural Language:* The adjunction lifts to the level of schemes. Since schemes are a full subcategory of locally ringed spaces, the adjunction can be transported, giving us the fundamental $\Gamma \dashv \mathrm{Spec}$ adjunction in the category of schemes.

= Adjunction Properties and Applications

== Home-Set Bijection

```lean
theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Spec.obj R) :
    ΓSpec.adjunction.homEquiv X R f = ⟨locallyRingedSpaceAdjunction.homEquiv X.1 R f⟩

lemma ΓSpec_adjunction_homEquiv_eq {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = (Scheme.ΓSpecIso B).hom ≫ φ
```

*Natural Language:* The adjunction provides a natural bijection between morphisms $X \to \mathrm{Spec}(R)$ and ring homomorphisms $R \to \Gamma(X, \mathcal{O}_X)$. The explicit formula shows how to translate between geometric morphisms and algebraic homomorphisms.

== Counit Properties

```lean
instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply @NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance
```

*Natural Language:* The counit of the adjunction is a natural isomorphism. This means that every commutative ring is naturally isomorphic to the global sections of its spectrum, establishing the equivalence between rings and global sections of affine schemes.

= Immediate Consequences

== Fully Faithful Spec

```lean
instance Spec.fullyFaithful : FullyFaithful (LocallyRingedSpace.Spec) :=
  ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

instance Scheme.Spec.fullyFaithful : FullyFaithful Scheme.Spec :=
  ΓSpec.adjunction.fullyFaithful_Of_IsIso_Counit
```

*Natural Language:* Since the counit is an isomorphism, the Spec functor is fully faithful. This means that the category of commutative rings (with arrows reversed) embeds as a full subcategory of locally ringed spaces/schemes.

== Reflective Subcategory

```lean
instance : IsReflectiveSubcategory LocallyRingedSpace.Spec := by
  apply IsReflectiveSubcategory.mk
  exact ⟨_, ΓSpec.locallyRingedSpaceAdjunction⟩

instance : IsReflectiveSubcategory Scheme.Spec := by
  apply IsReflectiveSubcategory.mk
  exact ⟨_, ΓSpec.adjunction⟩
```

*Natural Language:* The image of the Spec functor (i.e., affine schemes) forms a reflective subcategory. This means every locally ringed space/scheme has a "best affine approximation" given by $\mathrm{Spec}(\Gamma(X, \mathcal{O}_X))$.

= Technical Lemmas and Compatibilities

== Extension Properties

```lean
theorem comp_ring_hom_ext {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
    {g : X ⟶ Spec.locallyRingedSpaceObj R} (h : g.c.app (op ⊤) = f) :
    f ≫ X.toΓSpec.c.app (op ⊤) = g.c.app (op ⊤) ≫ Spec.map f.c.app (op ⊤)
```

*Natural Language:* Technical compatibility results that ensure the adjunction works correctly with composition and various natural transformations. These are essential for proving the triangle identities and other properties.

== Naturality of Constructions

```lean
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality := -- proof that this is natural in X
```

*Natural Language:* The unit of the adjunction is natural: it commutes with morphisms of locally ringed spaces in the expected way. This naturality is crucial for the adjunction to be well-defined.

= Conclusion

The $\Gamma$-$\mathrm{Spec*$ adjunction is fundamental to algebraic geometry, establishing the precise relationship between:

\item *Geometric objects*: Locally ringed spaces and schemes
\item *Algebraic objects*: Commutative rings
\item *Geometric morphisms*: Morphisms of locally ringed spaces/schemes
\item *Algebraic morphisms*: Ring homomorphisms (in opposite direction)

Key insights:
\item Every locally ringed space has a canonical map to the spectrum of its global sections
\item Every ring is naturally isomorphic to the global sections of its spectrum
\item These relationships are functorial and satisfy compatibility conditions
\item The affine world (spectra of rings) sits inside the general world as a reflective subcategory

This adjunction provides the foundation for understanding how algebraic properties translate to geometric properties and vice versa, making it possible to use algebraic methods to solve geometric problems and geometric intuition to understand algebraic phenomena.
