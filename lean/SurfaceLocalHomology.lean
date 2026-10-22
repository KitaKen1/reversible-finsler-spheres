import TauCeti.AlgebraicTopology.Singular.DiskSphere
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.Excision
import TauCeti.Topology.Homotopy.PuncturedStarConvex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The nonzero local class at a strict maximum

The inclusion from a disk modulo its boundary to the same disk modulo its
puncture induces an isomorphism on relative singular homology. This follows
from radial deformation of the punctured disk, the long exact sequence of
a pair, and Tau Ceti's disk homology calculation.

The resulting class can be detected by a continuous coordinate projection.
This is the topological part of the local Morse construction. It constructs
a nonzero class from geometric coordinate and energy hypotheses; it does
not construct the required chart for an arbitrary geodesic.
-/

namespace Finsler.SurfaceLocalHomology

open CategoryTheory CategoryTheory.Limits HomologicalComplex Metric Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

abbrev Disk (q : ℕ) := ↥(TopCat.disk.{0} q)
abbrev Boundary (q : ℕ) := ↥(TopCat.diskBoundary.{0} q)

/-- The Euclidean coordinates of a point in the standard disk. -/
def coordinates (q : ℕ) : C(Disk q, EuclideanSpace ℝ (Fin q)) :=
  ⟨fun x => x.down.val, continuous_subtype_val.comp continuous_uliftDown⟩

def center (q : ℕ) : Disk q := ⟨⟨0, by simp⟩⟩

theorem coordinates_eq_zero_iff (q : ℕ) (x : Disk q) :
    coordinates q x = 0 ↔ x = center q := by
  constructor
  · intro h
    apply ULift.ext
    exact Subtype.ext h
  · rintro rfl
    rfl

def punctured (q : ℕ) : Set (Disk q) := {x | coordinates q x ≠ 0}

def puncturedPair (q : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.disk q) (punctured q)

private def puncturedHomeomorph (q : ℕ) :
    punctured q ≃ₜ ↥(closedBall (0 : EuclideanSpace ℝ (Fin q)) 1 \ {0}) where
  toFun x := ⟨x.val.down.val, x.val.down.property, x.property⟩
  invFun x := ⟨⟨⟨x.val, x.property.1⟩⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    exact ((coordinates q).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_uliftUp.comp (continuous_subtype_val.subtype_mk _)

/-- Radial deformation identifies the punctured disk with its boundary. -/
def boundaryEquiv (q : ℕ) : ContinuousMap.HomotopyEquiv (Boundary q) (punctured q) :=
  Homeomorph.ulift.toHomotopyEquiv |>.trans
    (((convex_closedBall (0 : EuclideanSpace ℝ (Fin q)) 1).starConvex
      (by simp)).sphereHomotopyEquiv zero_lt_one sphere_subset_closedBall) |>.trans
        (puncturedHomeomorph q).symm.toHomotopyEquiv

/-- Enlarge the lower subspace of a disk from its boundary to its puncture. -/
def boundaryToPunctured (q : ℕ) : TauCeti.diskBoundaryPair q ⟶ puncturedPair q :=
  TopPair.ofHom (𝟙 (TopCat.disk q)) (TopCat.ofHom (boundaryEquiv q).toFun)
    (by ext x; rfl)

private theorem quasiIso_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (K : Type) [Field K] :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom e.toFun)) (ModuleCat.of K K)) := by
  apply (quasiIso_iff _).mpr
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
  change IsIso (e.singularHomologyIso (ModuleCat.of K K) i).hom
  infer_instance

/-- Equivalences on the ambient spaces and the subspaces induce relative
homology isomorphisms, even if their homotopy inverses do not form a pair map. -/
theorem isIso_relative_of_equivalences {P Q : TopPair} (f : P ⟶ Q)
    (e : ContinuousMap.HomotopyEquiv P.fst Q.fst)
    (e' : ContinuousMap.HomotopyEquiv P.snd Q.snd)
    (he : TopPair.Hom.fst f = TopCat.ofHom e.toFun)
    (he' : TopPair.Hom.snd f = TopCat.ofHom e'.toFun)
    (K : Type) [Field K] (q : ℕ) :
    IsIso (TopPair.singularHomologyMap f (ModuleCat.of K K) q) := by
  have hleft : QuasiIso (SSet.chainComplexMap (TopPair.toSSetPair.map f).left
      (ModuleCat.of K K)) := by
    rw [TopPair.toSSetPair_map_left, he']
    exact quasiIso_of_homotopyEquiv e' K
  have hright : QuasiIso (SSet.chainComplexMap (TopPair.toSSetPair.map f).right
      (ModuleCat.of K K)) := by
    rw [TopPair.toSSetPair_map_right, he]
    exact quasiIso_of_homotopyEquiv e K
  exact SSetPair.isIso_homologyMap_of_quasiIso (TopPair.toSSetPair.map f) (ModuleCat.of K K) q

/-- The boundary-to-puncture inclusion is an isomorphism in every degree. -/
theorem isIso_boundaryToPunctured (q : ℕ) (K : Type) [Field K] (j : ℕ) :
    IsIso (TopPair.singularHomologyMap (boundaryToPunctured q) (ModuleCat.of K K) j) :=
  isIso_relative_of_equivalences _ (ContinuousMap.HomotopyEquiv.refl (Disk q))
    (boundaryEquiv q) rfl rfl K j

/-- The standard top-degree disk class, over any field of coefficients. -/
def diskClass (q : ℕ) (K : Type) [Field K] :
    ↥((TauCeti.diskBoundaryPair q).singularHomology (ModuleCat.of K K) q) :=
  (TauCeti.singularHomologyDiskBoundaryPairIso (ModuleCat.of K K) q).inv (1 : K)

theorem diskClass_ne_zero (q : ℕ) (K : Type) [Field K] : diskClass q K ≠ 0 := by
  intro h
  let e := TauCeti.singularHomologyDiskBoundaryPairIso (ModuleCat.of K K) q
  have hi : e.hom (e.inv (1 : K)) = 1 := ConcreteCategory.congr_hom e.inv_hom_id 1
  have hh := congrArg (fun x => e.hom x) h
  change e.hom (e.inv 1) = e.hom 0 at hh
  rw [hi, map_zero] at hh
  exact one_ne_zero hh

/-- The explicit disk class remains nonzero after replacing the boundary
by every point except the center. -/
theorem puncturedClass_ne_zero (q : ℕ) (K : Type) [Field K] :
    TopPair.singularHomologyMap (boundaryToPunctured q) (ModuleCat.of K K) q
      (diskClass q K) ≠ 0 := by
  have := isIso_boundaryToPunctured q K q
  have hinj := (ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap (boundaryToPunctured q) (ModuleCat.of K K) q)).1
  intro h
  apply diskClass_ne_zero q K
  apply hinj
  simpa only [map_zero] using h

/-- A coordinate detector of the punctured-disk class proves nonvanishing
in any target pair. The commutative diagram is a statement about actual
continuous maps of pairs, before applying homology. -/
theorem detectedClass_ne_zero {P : TopPair} {q : ℕ}
    (f : TauCeti.diskBoundaryPair q ⟶ P) (r : P ⟶ puncturedPair q)
    (hr : f ≫ r = boundaryToPunctured q) (K : Type) [Field K] :
    TopPair.singularHomologyMap f (ModuleCat.of K K) q (diskClass q K) ≠ 0 := by
  have hh := congrArg (fun g => TopPair.singularHomologyMap g (ModuleCat.of K K) q) hr
  rw [TopPair.singularHomologyMap_comp] at hh
  intro hz
  apply puncturedClass_ne_zero q K
  have he := ConcreteCategory.congr_hom hh (diskClass q K)
  change TopPair.singularHomologyMap r (ModuleCat.of K K) q
    (TopPair.singularHomologyMap f (ModuleCat.of K K) q (diskClass q K)) = _ at he
  rw [hz, map_zero] at he
  exact he.symm

theorem boundary_ne_center (q : ℕ) (x : Boundary q) :
    TopCat.diskBoundaryInclusion q x ≠ center q := by
  intro h
  have hz := congrArg (coordinates q) h
  have hx := x.down.property
  change coordinates q (TopCat.diskBoundaryInclusion q x) = 0 at hz
  change dist x.down.val 0 = 1 at hx
  change x.down.val = 0 at hz
  rw [hz, dist_self] at hx
  exact zero_ne_one hx

section Detector

variable {X : Type} [TopologicalSpace X] {q : ℕ} (E : X → ℝ) (c : ℝ)

/-- A local neighborhood relative to its strict lower-energy part. -/
def energyPair : TopPair := TopPair.ofSubset (X := TopCat.of X) {x | E x < c}

/-- A disk whose boundary lies strictly below the reference energy. -/
def familyMap (f : C(Disk q, X))
    (hb : ∀ x : Boundary q, E (f (TopCat.diskBoundaryInclusion q x)) < c) :
    TauCeti.diskBoundaryPair q ⟶ energyPair E c :=
  TopPair.ofHom (TopCat.ofHom f)
    (TopCat.ofHom ⟨fun x => ⟨f (TopCat.diskBoundaryInclusion q x), hb x⟩,
      (f.continuous.comp (TopCat.diskBoundaryInclusion q).hom.continuous).subtype_mk _⟩)
    (by ext x; rfl)

/-- Coordinate projection to the disk, with lower energy avoiding its center. -/
def projectionMap (r : C(X, Disk q))
    (hd : ∀ x, E x < c → r x ∈ punctured q) :
    energyPair E c ⟶ puncturedPair q :=
  TopPair.ofHom (TopCat.ofHom r)
    (TopCat.ofHom ⟨fun x => ⟨r x.val, hd x.val x.property⟩,
      (r.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (by ext x; rfl)

/-- A lower-energy point cannot lie in the fiber of a fiberwise minimum. -/
theorem detector_of_fiber_minimum (r : C(X, Disk q))
    (hmin : ∀ x, r x = center q → c ≤ E x) :
    ∀ x, E x < c → r x ∈ punctured q := by
  intro x hx hz
  exact (not_le_of_gt hx) (hmin x ((coordinates_eq_zero_iff q (r x)).mp hz))

theorem familyMap_projectionMap (f : C(Disk q, X)) (r : C(X, Disk q))
    (hb : ∀ x : Boundary q, E (f (TopCat.diskBoundaryInclusion q x)) < c)
    (hd : ∀ x, E x < c → r x ∈ punctured q)
    (hr : ∀ x, r (f x) = x) :
    familyMap E c f hb ≫ projectionMap E c r hd = boundaryToPunctured q := by
  ext : 1
  · ext x
    apply Subtype.ext
    exact hr (TopCat.diskBoundaryInclusion q x)
  · ext x
    exact hr x

/-- The disk fundamental class is nonzero in the actual local energy pair.
The hypotheses concern a continuous coordinate projection and energy, not
an assumed homology class or an assumed nonzero induced map. -/
theorem localClass_ne_zero (f : C(Disk q, X)) (r : C(X, Disk q))
    (hb : ∀ x : Boundary q, E (f (TopCat.diskBoundaryInclusion q x)) < c)
    (hmin : ∀ x, r x = center q → c ≤ E x)
    (hr : ∀ x, r (f x) = x) (K : Type) [Field K] :
    TopPair.singularHomologyMap (familyMap E c f hb) (ModuleCat.of K K) q
      (diskClass q K) ≠ 0 := by
  let hd := detector_of_fiber_minimum E c r hmin
  exact detectedClass_ne_zero _ (projectionMap E c r hd)
    (familyMap_projectionMap E c f r hb hd hr) K

theorem familyMap_homology_ne_zero (f : C(Disk q, X)) (r : C(X, Disk q))
    (hb : ∀ x : Boundary q, E (f (TopCat.diskBoundaryInclusion q x)) < c)
    (hmin : ∀ x, r x = center q → c ≤ E x)
    (hr : ∀ x, r (f x) = x) (K : Type) [Field K] :
    TopPair.singularHomologyMap (familyMap E c f hb) (ModuleCat.of K K) q ≠ 0 := by
  intro h
  apply localClass_ne_zero E c f r hb hmin hr K
  rw [h]
  rfl

end Detector

section CriticalPoint

variable {X : Type} [TopologicalSpace X] {q : ℕ} (E : X → ℝ)

/-- The strict lower sublevel with just the critical point adjoined, as used
in the definition of local critical homology. -/
def criticalCarrier (p : X) : Set X := {x | E x < E p ∨ x = p}

/-- The same maximal disk, now valued in the critical carrier rather than
the full neighborhood. Every point except its center has lower energy. -/
def criticalFamily (f : C(Disk q, X))
    (hmax : ∀ x, x ≠ center q → E (f x) < E (f (center q))) :
    C(Disk q, criticalCarrier E (f (center q))) := by
  classical
  have hf : ∀ x, f x ∈ criticalCarrier E (f (center q)) := by
    intro x
    by_cases hx : x = center q
    · exact Or.inr (congrArg f hx)
    · exact Or.inl (hmax x hx)
  exact ⟨fun x => ⟨f x, hf x⟩, f.continuous.subtype_mk hf⟩

/-- The class is already nonzero in `(E < E(p)) ∪ {p}` relative to
`E < E(p)`. Points of higher energy are not needed to detect it. This is
the local critical homology used by the surface argument, still requiring
the geometric disk, coordinate projection and central-fiber minimum. -/
theorem criticalClass_ne_zero (f : C(Disk q, X)) (r : C(X, Disk q))
    (hmax : ∀ x, x ≠ center q → E (f x) < E (f (center q)))
    (hmin : ∀ x, r x = center q → E (f (center q)) ≤ E x)
    (hr : ∀ x, r (f x) = x) (K : Type) [Field K] :
    TopPair.singularHomologyMap
      (familyMap (fun x : criticalCarrier E (f (center q)) => E x.val) (E (f (center q)))
        (criticalFamily E f hmax) (fun x => hmax _ (boundary_ne_center q x)))
      (ModuleCat.of K K) q (diskClass q K) ≠ 0 := by
  apply localClass_ne_zero (fun x : criticalCarrier E (f (center q)) => E x.val)
    (E (f (center q))) _
    ⟨fun x => r x.val, r.continuous.comp continuous_subtype_val⟩
  · intro x hx
    exact hmin x.val hx
  · intro x
    exact hr x

/-- In the critical carrier, any open neighborhood of the critical point
and the strict lower sublevel form an open cover. -/
theorem criticalCarrier_cover (hE : Continuous E) (p : X) (U : Set X)
    (hU : IsOpen U) (hp : p ∈ U) :
    interior {x : criticalCarrier E p | x.val ∈ U} ∪
      interior {x : criticalCarrier E p | E x.val < E p} = univ := by
  have h₁ : IsOpen {x : criticalCarrier E p | x.val ∈ U} :=
    hU.preimage continuous_subtype_val
  have h₂ : IsOpen {x : criticalCarrier E p | E x.val < E p} :=
    isOpen_lt (hE.comp continuous_subtype_val) continuous_const
  rw [h₁.interior_eq, h₂.interior_eq]
  apply eq_univ_of_forall
  intro x
  rcases x.property with hx | hx
  · exact Or.inr hx
  · apply Or.inl
    change x.val ∈ U
    rw [hx]
    exact hp

/-- Localizing the critical carrier to any open neighborhood of its critical
point preserves homology in every degree. This supplies the actual excision
step, rather than assuming an injective local-to-global map. The global
target here adjoins only the critical point, not an entire upper sublevel. -/
theorem isIso_critical_excision (hE : Continuous E) (p : X) (U : Set X)
    (hU : IsOpen U) (hp : p ∈ U) (K : Type) [Field K] (j : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := TopCat.of (criticalCarrier E p))
        {x | x.val ∈ U} {x | E x.val < E p}) (ModuleCat.of K K) j) :=
  TopPair.isIso_singularHomologyMap_excisionMap (ModuleCat.of K K) _ _
    (criticalCarrier_cover E hE p U hU hp) j

/-- The critical pair, with the distinguished point adjoined to the strict
lower sublevel. -/
def criticalPair (p : X) : TopPair :=
  energyPair (fun x : criticalCarrier E p => E x.val) (E p)

/-- Inclusion of the critical carrier of an energy restricted to a
neighborhood into the original critical carrier. -/
def criticalInclusion (U : Set X) (p : U) :
    criticalPair (fun x : U => E x.val) p ⟶ criticalPair E p.val := by
  let f : C(criticalCarrier (fun x : U => E x.val) p, criticalCarrier E p.val) :=
    ⟨fun x => ⟨x.val.val, x.property.elim Or.inl (fun h => Or.inr (congrArg Subtype.val h))⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  exact TopPair.ofSubsetMap (TopCat.ofHom f) (fun _ h => h)

/-- The actual inclusion from a neighborhood critical pair is an
isomorphism on homology. This form avoids changing the nesting order of
subtypes when applying local coordinates in the neighborhood. -/
theorem isIso_criticalInclusion (hE : Continuous E) (U : Set X) (hU : IsOpen U)
    (p : U) (K : Type) [Field K] (j : ℕ) :
    IsIso (TopPair.singularHomologyMap (criticalInclusion E U p) (ModuleCat.of K K) j) := by
  let V : Bool → Set (criticalCarrier E p.val) :=
    fun b => if b then {x | x.val ∈ U} else {x | E x.val < E p.val}
  apply TopPair.isIso_singularHomologyMap_of_open_cover (ModuleCat.of K K)
    (criticalInclusion E U p) _ _ V _ _ _ j
  · exact (Topology.IsEmbedding.subtypeVal.comp
      Topology.IsEmbedding.subtypeVal).codRestrict _ _
  · rintro x ⟨y, hy⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    have h : E y.val.val < E p.val := y.property
    have he := congrArg (fun z : criticalCarrier E p.val => z.val) hy
    change y.val.val = x.val.val at he
    change E x.val.val < E p.val
    rw [← he]
    exact h
  · intro b
    cases b
    · exact isOpen_lt (hE.comp continuous_subtype_val) continuous_const
    · exact hU.preimage continuous_subtype_val
  · apply eq_univ_of_forall
    intro x
    rcases x.property with hx | hx
    · exact mem_iUnion.mpr ⟨false, hx⟩
    · exact mem_iUnion.mpr ⟨true, by change x.val ∈ U; rw [hx]; exact p.property⟩
  · intro b
    cases b
    · apply Or.inl
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · apply Or.inr
      intro x hx
      refine ⟨⟨⟨x.val, hx⟩, ?_⟩, ?_⟩
      · rcases x.property with h | h
        · exact Or.inl h
        · exact Or.inr (Subtype.ext h)
      · apply Subtype.ext
        rfl

end CriticalPoint

/-- An isolated strict maximum supplies the nonzero local class in its
own disk neighborhood, including the degree-zero case. -/
theorem strictMaximum_class_ne_zero {q : ℕ} (E : Disk q → ℝ)
    (hmax : ∀ x, x ≠ center q → E x < E (center q)) (K : Type) [Field K] :
    TopPair.singularHomologyMap
      (familyMap E (E (center q)) (ContinuousMap.id (Disk q))
        (fun x => hmax _ (boundary_ne_center q x))) (ModuleCat.of K K) q
      (diskClass q K) ≠ 0 := by
  apply localClass_ne_zero E (E (center q)) _ (ContinuousMap.id (Disk q))
  · intro x hx
    exact le_of_eq (congrArg E hx.symm)
  · intro x
    rfl

section Product

variable {q : ℕ} {Z : Type} [TopologicalSpace Z]

/-- The maximal disk in product coordinates for a local Morse model. -/
def productFamily (z₀ : Z) : C(Disk q, Disk q × Z) :=
  ⟨fun x => (x, z₀), continuous_id.prodMk continuous_const⟩

/-- A strict maximum on the central disk and a minimum on its transverse
central fiber produce an explicit nonzero relative homology class. The
transverse space can be infinite-dimensional, and the maximum can be
degenerate; no nondegeneracy of the reduced function is required. -/
theorem product_class_ne_zero (E : Disk q × Z → ℝ) (z₀ : Z)
    (hmax : ∀ x, x ≠ center q → E (x, z₀) < E (center q, z₀))
    (hmin : ∀ z, E (center q, z₀) ≤ E (center q, z))
    (K : Type) [Field K] :
    TopPair.singularHomologyMap
      (familyMap E (E (center q, z₀)) (productFamily z₀)
        (fun x => hmax _ (boundary_ne_center q x))) (ModuleCat.of K K) q
      (diskClass q K) ≠ 0 := by
  apply localClass_ne_zero E (E (center q, z₀)) _ ⟨Prod.fst, continuous_fst⟩
  · intro x hx
    change x.1 = center q at hx
    rcases x with ⟨x, z⟩
    dsimp at hx ⊢
    rw [hx]
    exact hmin z
  · intro x
    rfl

/-- Express the maximal disk in an actual topological coordinate chart. -/
def chartFamily {X : Type} [TopologicalSpace X] (e : Disk q × Z ≃ₜ X) (z₀ : Z) :
    C(Disk q, X) := (⟨e, e.continuous⟩ : C(Disk q × Z, X)).comp (productFamily z₀)

/-- Transfer the product-model generator through a chart to the original
energy function. Only the chart and the two energy inequalities are inputs;
the homology class and its nonvanishing are constructed. -/
theorem chart_class_ne_zero {X : Type} [TopologicalSpace X]
    (E : X → ℝ) (e : Disk q × Z ≃ₜ X) (z₀ : Z)
    (hmax : ∀ x, x ≠ center q → E (e (x, z₀)) < E (e (center q, z₀)))
    (hmin : ∀ z, E (e (center q, z₀)) ≤ E (e (center q, z)))
    (K : Type) [Field K] :
    TopPair.singularHomologyMap
      (familyMap E (E (e (center q, z₀))) (chartFamily e z₀)
        (fun x => hmax _ (boundary_ne_center q x))) (ModuleCat.of K K) q
      (diskClass q K) ≠ 0 := by
  apply localClass_ne_zero E (E (e (center q, z₀))) _
    ⟨fun x => (e.symm x).1, continuous_fst.comp e.symm.continuous⟩
  · intro x hx
    change (e.symm x).1 = center q at hx
    have he : e (center q, (e.symm x).2) = x := by
      rw [← hx]
      exact e.apply_symm_apply x
    exact (hmin (e.symm x).2).trans_eq (congrArg E he)
  · intro x
    change (e.symm (e (x, z₀))).1 = x
    rw [e.symm_apply_apply]

end Product

/-- Excision preserves the constructed class when the local neighborhood
and the strict lower sublevel have interiors covering the target space.
The cover hypothesis is explicit: nonvanishing in a local pair alone does
not imply nonvanishing in an arbitrary larger energy sublevel. -/
theorem excisedClass_ne_zero {X : Type} [TopologicalSpace X] {q : ℕ}
    (E : X → ℝ) (c : ℝ) (U : Set X)
    (hcover : interior U ∪ interior {x | E x < c} = univ)
    (f : C(Disk q, U)) (r : C(U, Disk q))
    (hb : ∀ x : Boundary q, E (f (TopCat.diskBoundaryInclusion q x)).val < c)
    (hmin : ∀ x : U, r x = center q → c ≤ E x.val)
    (hr : ∀ x, r (f x) = x) (K : Type) [Field K] :
    TopPair.singularHomologyMap
      (familyMap (fun x : U => E x.val) c f hb ≫
        TopPair.excisionMap (X := TopCat.of X) U {x | E x < c}) (ModuleCat.of K K) q
      (diskClass q K) ≠ 0 := by
  have := TopPair.isIso_singularHomologyMap_excisionMap
    (ModuleCat.of K K) (X := TopCat.of X) U {x | E x < c} hcover q
  have hi := (ConcreteCategory.bijective_of_isIso
    (TopPair.singularHomologyMap (TopPair.excisionMap (X := TopCat.of X)
      U {x | E x < c}) (ModuleCat.of K K) q)).1
  rw [TopPair.singularHomologyMap_comp]
  intro hz
  change TopPair.singularHomologyMap (TopPair.excisionMap (X := TopCat.of X)
    U {x | E x < c}) (ModuleCat.of K K) q
      (TopPair.singularHomologyMap (familyMap (fun x : U => E x.val) c f hb)
        (ModuleCat.of K K) q (diskClass q K)) = 0 at hz
  apply localClass_ne_zero (fun x : U => E x.val) c f r hb hmin hr K
  apply hi
  simpa only [map_zero] using hz

end
end Finsler.SurfaceLocalHomology
