#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Introduction

This document provides a natural language companion to the `Gluing.lean* file in Mathlib4. The file develops the theory of gluing schemes together from local pieces, which is fundamental to constructing global objects from local data. This includes both general gluing constructions and specialized "locally directed" gluing for certain well-behaved diagrams.

= The Glue Data Structure

== Definition of Glue Data

```lean
structure GlueData extends CategoryTheory.GlueData Scheme where
  f_open : ∀ i j, IsOpenImmersion (f i j)
```

*Natural Language:* A glue data for schemes consists of:
\item An index set $J$
\item Schemes $U_i$ for each $i \in J$ (the pieces to be glued)
\item Schemes $V_{ij*$ for each pair $(i,j)$ (the overlaps)
\item Open immersions $f_{ij*: V_{ij} \to U_i$
\item Transition maps $t_{ij*: V_{ij} \to V_{ji}$
\item Compatibility conditions ensuring the gluing is well-defined

The key additional requirement is that all the maps $f_{ij*$ are open immersions, preserving the geometric structure.

== Glue Data Hierarchy

```lean
abbrev toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }
```

*Natural Language:* The gluing construction for schemes builds on gluing constructions for locally ringed spaces, sheafed spaces, and presheafed spaces. This hierarchical approach ensures that all the relevant structure is properly preserved.

= The Glued Scheme Construction

== Implementation Details

```lean
def gluedScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  refine ⟨_, ((D.U i).affineCover.map y).toLRSHom ≫
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i, ?_⟩
  ...
```

*Natural Language:* The glued scheme is constructed by first creating the glued locally ringed space, then verifying that every point has an affine neighborhood. This uses the fact that each piece $U_i$ has an affine cover, and these covers can be transferred to the glued space.

== Main Definition

```lean
abbrev glued : Scheme := 𝖣.glued
```

*Natural Language:* The glued scheme $D.glued$ is the result of gluing together all the schemes $U_i$ according to the glue data $D$.

= Inclusion Morphisms

== The Inclusion Maps

```lean
abbrev ι (i : D.J) : D.U i ⟶ D.glued := 𝖣.ι i
```

*Natural Language:* For each index $i$, there is a canonical inclusion morphism $\iota_i: U_i \to D.glued$ that embeds the $i$-th piece into the glued scheme.

== Open Immersion Property

```lean
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i)
```

*Natural Language:* Each inclusion $\iota_i: U_i \to D.glued$ is an open immersion, meaning that $U_i$ appears as an open subscheme of the glued space.

== Joint Surjectivity

```lean
theorem ι_jointly_surjective (x : 𝖣.glued.carrier) :
    ∃ (i : D.J) (y : (D.U i).carrier), (D.ι i).base y = x
```

*Natural Language:* The inclusion maps are jointly surjective, meaning every point of the glued scheme comes from some piece $U_i$. This shows that the gluing covers the entire space.

= Gluing Conditions

== Basic Glue Condition

```lean
@[simp (high), reassoc]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
```

*Natural Language:* The fundamental gluing condition states that the two ways of mapping from $V_{ij}$ to the glued space (via $U_i$ or via $U_j$) agree. This ensures that the overlaps are consistently identified.

== Pullback Characterization

```lean
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

def vPullbackConeIsLimit (i j : D.J) : IsLimit (D.vPullbackCone i j)
```

*Natural Language:* The overlap $V_{ij}$ is precisely the intersection $U_i \cap U_j$ in the glued space. This is expressed by saying that $V_{ij}$ with its maps to $U_i$ and $U_j$ forms a pullback square.

= Topological Properties

== Carrier Isomorphism

```lean
def isoCarrier : D.glued.carrier ≅ (D_).glued
```

*Natural Language:* The underlying topological space of the glued scheme is isomorphic to the gluing of the underlying topological spaces of the pieces. This shows that the scheme-theoretic gluing correctly captures the topological gluing.

== Point Identification

```lean
def Rel (a b : Σ i, ((D.U i).carrier : Type _)) : Prop :=
  ∃ x : (D.V (a.1, b.1)).carrier, (D.f _ _).base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).base x = b.2
```

*Natural Language:* Points $x \in U_i$ and $y \in U_j$ are identified in the glued space if and only if there exists a point in $V_{ij}$ that maps to $x$ under $f_{ij}$ and to $y$ under the composition $t_{ij} \circ f_{ji}$.

== Open Set Characterization

```lean
theorem isOpen_iff (U : Set D.glued.carrier) : IsOpen U ↔ ∀ i, IsOpen ((D.ι i).base ⁻¹' U)
```

*Natural Language:* A subset of the glued space is open if and only if its preimage in each piece $U_i$ is open. This gives a practical criterion for checking openness in glued schemes.

= Open Covers from Glue Data

== The Natural Cover

```lean
@[simps -isSimp]
def openCover (D : Scheme.GlueData) : OpenCover D.glued where
  J := D.J
  obj := D.U
  map := D.ι
  f x := (D.ι_jointly_surjective x).choose
  covers x := ⟨_, (D.ι_jointly_surjective x).choose_spec.choose_spec⟩
```

*Natural Language:* The pieces $U_i$ naturally form an open cover of the glued scheme $D.glued$, with the inclusion maps serving as the cover morphisms.

= Gluing from Open Covers

== Cover to Glue Data

```lean
@[simps]
def gluedCover : Scheme.GlueData.{u} where
  J := 𝒰.J
  U := 𝒰.obj
  V := fun ⟨x, y⟩ => pullback (𝒰.map x) (𝒰.map y)
  f _ _ := pullback.fst _ _
  t _ _ := (pullbackSymmetry _ _).hom
  ...
```

*Natural Language:* Given an open cover $\mathcal{U} = \{U_i\}$ of a scheme $X$, we can construct glue data where the overlaps $V_{ij}$ are the pullbacks (intersections) $U_i \times_X U_j$.

== Recovery Isomorphism

```lean
def fromGlued : 𝒰.gluedCover.glued ⟶ X
instance : IsIso 𝒰.fromGlued
```

*Natural Language:* The gluing of an open cover of $X$ is canonically isomorphic to $X$ itself. The canonical morphism $\mathcal{U}.gluedCover.glued \to X$ is an isomorphism.

= Gluing Morphisms

== Compatible Morphism Gluing

```lean
def glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme.{u}} (f : ∀ x, 𝒰.obj x ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x = pullback.snd _ _ ≫ f y) :
    X ⟶ Y
```

*Natural Language:* Given morphisms $f_i: U_i \to Y$ that agree on overlaps (i.e., are compatible), we can glue them together to get a global morphism $X \to Y$.

== Morphism Extension Property

```lean
theorem hom_ext (𝒰 : OpenCover.{v} X) {Y : Scheme} (f₁ f₂ : X ⟶ Y)
    (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂
```

*Natural Language:* Two morphisms $f_1, f_2: X \to Y$ are equal if they agree when restricted to each element of an open cover. This is a fundamental "local-to-global" principle.

= Locally Directed Gluing

== Locally Directed Diagrams

```lean
variable {J : Type w} [Category.{v} J] (F : J ⥤ Scheme.{u})
variable [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
variable [(F ⋙ forget).IsLocallyDirected]
```

*Natural Language:* A diagram $F: J \to \mathbf{Scheme}$ is locally directed if:
\item All morphisms in the diagram are open immersions
\item For any schemes $F(i)$, $F(j)$ and points $x \in F(i)$, $y \in F(j)$ that map to the same point in the colimit, there exists $F(k)$ containing both points

== Intersection Construction

```lean
def V (i j : J) : (F.obj i).Opens := ⨆ (k : Σ k, (k ⟶ i) × (k ⟶ j)), (F.map k.2.1).opensRange
```

*Natural Language:* The "intersection" $V_{ij}$ is defined as the union of all schemes $F(k)$ that map to both $F(i)$ and $F(j)$. This captures the overlapping regions in a directed system.

== Glue Data Construction

```lean
def glueData : Scheme.GlueData where
  J := Shrink.{u} J
  U j := F.obj ↓j
  V ij := V F ↓ij.1 ↓ij.2
  f i j := Scheme.Opens.ι _
  t i j := t F ↓i ↓j
  ...
```

*Natural Language:* For a locally directed diagram, we can automatically construct glue data using the intersection construction. The transition maps are induced by the local directedness property.

== Colimit Construction

```lean
def cocone : Cocone F where
  pt := (glueData F).glued
  ι.app j := F.map (eqToHom (by simp)) ≫ (glueData F).ι (equivShrink _ j)

def isColimit : IsColimit (cocone F)
```

*Natural Language:* The glued scheme serves as the colimit of the locally directed diagram, with the natural morphisms from each component scheme.

= Applications and Importance

== General Gluing Applications

The general gluing theory enables:
\item Construction of schemes from local affine pieces
\item Proof that many constructions preserve the scheme property
\item Development of descent theory and faithfully flat covers
\item Construction of moduli spaces and parameter spaces

== Locally Directed Applications

The locally directed gluing is particularly useful for:
\item Union of schemes indexed by directed sets
\item Direct limits in the category of schemes
\item Constructions involving increasing sequences of open sets
\item Algebraic closures and separable closures of schemes

== Connection to Classical Algebraic Geometry

This gluing theory formalizes several classical constructions:
\item Patching together affine charts to build projective varieties
\item Constructing schemes from sheaves of rings
\item Building global sections from compatible local sections
\item Descent for morphisms and other properties

= Technical Implementation

== Multicoequalizer Construction

The gluing is implemented using multicoequalizers in the category of schemes:
\item The coequalizer identifies points that should be the same
\item Open immersions ensure the gluing preserves the scheme structure
\item Compatibility conditions ensure well-definedness

== Hierarchy of Constructions

The construction builds through several levels:
\item Topological gluing of underlying spaces
\item Presheafed space gluing with compatible structure sheaves
\item Sheafed space gluing with sheaf conditions
\item Locally ringed space gluing with local ring conditions
\item Scheme gluing with additional scheme-theoretic properties

= Conclusion

The gluing theory in `Gluing.lean* provides:

== Fundamental Constructions

\item General framework for gluing schemes from local pieces
\item Specialized efficient methods for directed diagrams
\item Tools for extending local morphisms to global ones
\item Characterizations of topological and algebraic properties

== Theoretical Foundations

\item Rigorous treatment of the local-to-global principle
\item Proof that schemes can be reconstructed from their open covers
\item Foundation for descent theory and faithfully flat morphisms
\item Connection between categorical limits and geometric constructions

== Practical Tools

\item Concrete algorithms for checking gluing conditions
\item Methods for extending local constructions globally
\item Tools for working with covers and intersection conditions
\item Efficient handling of directed systems and unions

This gluing theory is essential for algebraic geometry, providing both the theoretical framework and practical tools needed to construct and study schemes systematically.
