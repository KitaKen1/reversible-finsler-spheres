module

public import Finsler.Topology.BorelK
public import Finsler.Analysis.IntervalH1HalfRootCuts

/-! The fixed-locus formula. On the half-shift fixed part of a sublevel the half-shift acts
trivially, so the K-Borel cohomology of (X^τ_b ∪ M, M) splits as ∏_{l ≤ J} of its reflection
Borel cohomology. Doubling of loops commutes with the reversal (the reversal of a loop is
t ↦ γ(−t) on the real line) and fixes constant loops, and it identifies (t_a, M) with the
fixed pair at level 2a; hence H^J_K(X^τ_{2a}, M) ≅ ∏_{l ≤ J} B^l_a. -/

@[expose] public section

namespace Finsler.BorelFixed

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevReverse Finsler.SobolevReflectionAction Finsler.SobolevCircleRepresentative
open Finsler.SobolevIteration Finsler.SobolevHalfRoot Finsler.SobolevCircleAction

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

theorem realMap_add_int (u : periodicSubmodule n) (x : ℝ) (m : ℤ) :
    realMap u (x + m) = realMap u x := by
  have h := (realMap_periodic u).int_mul m x
  simpa using h

theorem realMap_eq_fract (u : periodicSubmodule n) (x : ℝ) :
    realMap u x = continuousRepresentative (u : Space n) (Int.fract x) := by
  have hy : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [← realMap_eqOn u hy, ← realMap_add_int u (Int.fract x) ⌊x⌋, Int.fract_add_floor]

/-- On the real line the reversal is t ↦ −t. -/
theorem realMap_reverse (u : SphereLoop n) (x : ℝ) :
    realMap (reverseSphere u).data x = realMap u.data (-x) := by
  have hy : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hy' : 1 - Int.fract x ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [Int.fract_lt_one x], by linarith [Int.fract_nonneg x]⟩
  rw [realMap_eq_fract]
  change continuousRepresentative (reverseData (u.data : Space n)) (Int.fract x) = _
  rw [representative_reverseData _ hy]
  change continuousRepresentative _ (1 - Int.fract x) = _
  rw [← realMap_eqOn _ hy']
  have h2 : 1 - Int.fract x = -x + ((⌊x⌋ + 1 : ℤ) : ℝ) := by
    simp only [Int.fract]
    push_cast
    ring
  rw [h2, realMap_add_int]

theorem iterate_data (u : SphereLoop n) (k : ℕ) (hk : k ≠ 0) :
    ((iterateSphere u k hk).data : Space n) = iterateData u.data k hk := rfl

/-- Doubling commutes with the reversal. -/
theorem reverse_double (u : SphereLoop n) :
    reverseSphere (iterateSphere u 2 (by norm_num)) =
      iterateSphere (reverseSphere u) 2 (by norm_num) := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  have ht := t.2
  change continuousRepresentative (reverseData ((iterateSphere u 2 (by norm_num)).data : Space n)) t =
    continuousRepresentative (iterateData (reverseSphere u).data 2 (by norm_num)) t
  rw [representative_reverseData _ ht, iterate_data, representative_iterateData _ 2 _
    (reflection_mem_Icc ht), representative_iterateData _ 2 _ ht, realMap_reverse]
  have h : ((2 : ℕ) : ℝ) * reflection (t : ℝ) = -(((2 : ℕ) : ℝ) * (t : ℝ)) + ((2 : ℤ) : ℝ) := by
    simp only [reflection]
    push_cast
    ring
  rw [h, realMap_add_int]

/-- Doubling fixes constant loops. -/
theorem double_const (x : Sphere n) :
    iterateSphere (constantSphereLoop x) 2 (by norm_num) = constantSphereLoop x := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  have ht := t.2
  have hfr : Int.fract (((2 : ℕ) : ℝ) * (t : ℝ)) ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  change continuousRepresentative (iterateData (constantSphereLoop x).data 2 (by norm_num)) t =
    continuousRepresentative ((constantSphereLoop x).data : Space n) t
  rw [representative_iterateData _ 2 _ ht, realMap_eq_fract]
  change continuousRepresentative (constantData (x : Ambient n)) _ =
    continuousRepresentative (constantData (x : Ambient n)) t
  rw [continuousRepresentative_constantData _ hfr, continuousRepresentative_constantData _ ht]

theorem const_mem_halfFixed (x : Sphere n) : constantSphereLoop x ∈ halfFixedSet n :=
  constant_vadd half x

/-- The half-shift fixed part of the sublevel together with the constant loops. -/
def fixLev (b : ℝ) : Set (Loops n) := (energyCut F b ∩ halfFixedSet n) ∪ consts n

theorem consts_subset_fixLev (b : ℝ) : consts n ⊆ fixLev F b := subset_union_right

theorem fixLev_subset_halfFixed (b : ℝ) : fixLev F b ⊆ halfFixedSet n := by
  rintro u (hu | ⟨x, rfl⟩)
  · exact hu.2
  · exact const_mem_halfFixed x

theorem reverse_mem_halfFixed {u : SphereLoop n} (hu : u ∈ halfFixedSet n) :
    reverseSphere u ∈ halfFixedSet n := by
  change half +ᵥ reverseSphere u = reverseSphere u
  rw [← reverse_half]
  exact congrArg reverseSphere hu

theorem reverse_mem_fixLev {b : ℝ} {u : SphereLoop n} (hu : u ∈ fixLev F b) :
    reverseSphere u ∈ fixLev F b := by
  rcases hu with ⟨hu1, hu2⟩ | hu
  · left
    refine ⟨?_, reverse_mem_halfFixed hu2⟩
    change Real.sqrt (energy F (reverseSphere u)) < b
    rw [energy_reverseSphere]
    exact hu1
  · exact Or.inr (reverse_mem_consts hu)

/-- The fixed pair. -/
abbrev fixPair (b : ℝ) : TopPair.{0} := pairOf (consts_subset_fixLev F b)

/-- The reversal on the fixed part. -/
def revFix (b : ℝ) : C(fixLev F b, fixLev F b) :=
  ⟨fun u => ⟨reverseSphere (u : SphereLoop n), reverse_mem_fixLev F u.2⟩,
    ((reverseSphere_continuous n).comp continuous_subtype_val).subtype_mk _⟩

/-- The reversal of the fixed pair. -/
def revFixPair (b : ℝ) : fixPair F b ⟶ fixPair F b :=
  pairMap _ _ (revFix F b) (fun _ hx => reverse_mem_consts hx)

theorem revFixPair_sq (b : ℝ) : revFixPair F b ≫ revFixPair F b = 𝟙 (fixPair F b) := by
  have h : (revFix F b).comp (revFix F b) = ContinuousMap.id (fixLev F b) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverseSphere_involutive (u : SphereLoop n)) :
      (⟨reverseSphere (reverseSphere (u : SphereLoop n)), _⟩ : fixLev F b) = u)
  exact (pairMap_comp (consts_subset_fixLev F b) (consts_subset_fixLev F b)
    (consts_subset_fixLev F b) (revFix F b) (revFix F b) (fun _ hx => reverse_mem_consts hx)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

/-- The reflection cochains of the fixed pair. -/
abbrev fixComplex (b : ℝ) : InvComplex := ofPair (fixPair F b) (revFixPair F b) (revFixPair_sq F b)

/-- The half-shift acts trivially on the fixed pair. -/
def trivialCommuting (b : ℝ) : Commuting (fixComplex F b) where
  s _ := LinearMap.id
  ss _ _ := rfl
  sd _ _ := rfl
  st _ _ := rfl

/-- The K-cochains of the fixed pair. -/
abbrev kFix (b : ℝ) : InvComplex := borelInv (trivialCommuting F b)

theorem kFix_trivial (b : ℝ) : ∀ j x, (kFix F b).t j x = x := by
  intro j x
  apply Subtype.ext
  funext i
  rfl

/-- The fixed-locus splitting: H^J_K of the fixed pair is ∏_{l ≤ J} of its reflection Borel
cohomology. -/
def fixedSplit (b : ℝ) (J : ℕ) :
    HR (kFix F b) J ≃ₗ[ZMod 2] ((l : Fin (J + 1)) → HR (fixComplex F b) l) :=
  (splitEquiv (kFix F b) (kFix_trivial F b) J).trans
    (LinearEquiv.piCongrRight fun l => cohomologyEquiv (trivialCommuting F b) l)

/-- Doubling maps the sublevel at a into the fixed part at 2a. -/
theorem double_mem_fixLev {a : ℝ} {u : SphereLoop n} (hu : u ∈ lev F a) :
    (doubleSphere u : SphereLoop n) ∈ fixLev F (2 * a) := by
  rcases hu with hu | ⟨x, rfl⟩
  · left
    have h := (doubleSphere_mem_halfFixedCut_iff F a u).mpr hu
    exact ⟨h, (doubleSphere u).2⟩
  · right
    refine ⟨x, ?_⟩
    rw [doubleSphere_val, double_const]

/-- The root of a fixed loop of the fixed part at 2a lies in the sublevel at a. -/
theorem root_mem_lev {a : ℝ} {u : SphereLoop n} (hu : u ∈ fixLev F (2 * a)) :
    rootSphere ⟨u, fixLev_subset_halfFixed F (2 * a) hu⟩ ∈ lev F a := by
  rcases hu with ⟨hu1, hu2⟩ | ⟨x, rfl⟩
  · left
    exact (rootSphere_mem_energyCut_iff F a ⟨u, _⟩).mpr hu1
  · right
    refine ⟨x, ?_⟩
    apply iterateSphere_injective n 2 (by norm_num)
    change iterateSphere (constantSphereLoop x) 2 _ =
      iterateSphere (rootSphere ⟨constantSphereLoop x, _⟩) 2 _
    rw [double_const]
    exact (congrArg Subtype.val (double_rootSphere ⟨constantSphereLoop x, _⟩)).symm

/-- Doubling as a continuous map of the sets. -/
def dblMap (a : ℝ) : C(lev F a, fixLev F (2 * a)) where
  toFun u := ⟨(doubleSphere (u : SphereLoop n) : SphereLoop n), double_mem_fixLev F u.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp ((doubleSphere_continuous n).comp continuous_subtype_val)

/-- The root as a continuous map of the sets. -/
def rootMap (a : ℝ) : C(fixLev F (2 * a), lev F a) where
  toFun u := ⟨rootSphere ⟨(u : SphereLoop n), fixLev_subset_halfFixed F (2 * a) u.2⟩,
    root_mem_lev F u.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (rootSphere_continuous n).comp (continuous_subtype_val.subtype_mk _)

theorem dbl_mem_consts {a : ℝ} (u : lev F a) (hu : (u : Loops n) ∈ consts n) :
    ((dblMap F a u : fixLev F (2 * a)) : Loops n) ∈ consts n := by
  obtain ⟨x, hx⟩ := hu
  refine ⟨x, ?_⟩
  change constantSphereLoop x = (doubleSphere (u : SphereLoop n) : SphereLoop n)
  rw [← hx, doubleSphere_val, double_const]

theorem root_mem_consts {a : ℝ} (u : fixLev F (2 * a)) (hu : (u : Loops n) ∈ consts n) :
    ((rootMap F a u : lev F a) : Loops n) ∈ consts n := by
  obtain ⟨x, hx⟩ := hu
  refine ⟨x, ?_⟩
  apply iterateSphere_injective n 2 (by norm_num)
  change iterateSphere (constantSphereLoop x) 2 _ =
    iterateSphere (rootSphere ⟨(u : SphereLoop n), _⟩) 2 _
  rw [double_const]
  have h2 := congrArg Subtype.val (double_rootSphere ⟨(u : SphereLoop n),
    fixLev_subset_halfFixed F (2 * a) u.2⟩)
  exact hx.trans h2.symm

/-- Doubling as a map of pairs. -/
def dblPair (a : ℝ) : levPair F a ⟶ fixPair F (2 * a) :=
  pairMap _ _ (dblMap F a) (dbl_mem_consts F)

/-- The root as a map of pairs. -/
def rootPair (a : ℝ) : fixPair F (2 * a) ⟶ levPair F a :=
  pairMap _ _ (rootMap F a) (root_mem_consts F)

theorem dbl_root (a : ℝ) : dblPair F a ≫ rootPair F a = 𝟙 (levPair F a) := by
  have h : (rootMap F a).comp (dblMap F a) = ContinuousMap.id (lev F a) := by
    ext u
    have e := root_doubleSphere (u : SphereLoop n)
    exact e
  exact (pairMap_comp _ _ _ (dblMap F a) (rootMap F a) (dbl_mem_consts F)
    (root_mem_consts F)).symm.trans ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem root_dbl (a : ℝ) : rootPair F a ≫ dblPair F a = 𝟙 (fixPair F (2 * a)) := by
  have h : (dblMap F a).comp (rootMap F a) = ContinuousMap.id (fixLev F (2 * a)) := by
    ext u
    have e := congrArg Subtype.val (double_rootSphere ⟨(u : SphereLoop n),
      fixLev_subset_halfFixed F (2 * a) u.2⟩)
    exact e
  exact (pairMap_comp _ _ _ (rootMap F a) (dblMap F a) (root_mem_consts F)
    (dbl_mem_consts F)).symm.trans ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem dblPair_rev (a : ℝ) : dblPair F a ≫ revFixPair F (2 * a) = revPair F a ≫ dblPair F a := by
  have h : (revFix F (2 * a)).comp (dblMap F a) = (dblMap F a).comp (revLev F a) := by
    ext u
    have e := reverse_double (u : SphereLoop n)
    exact e
  exact (pairMap_comp _ _ _ (dblMap F a) (revFix F (2 * a)) (dbl_mem_consts F)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun u hx => dbl_mem_consts F _ (reverse_mem_consts hx))).trans
      (pairMap_comp _ _ _ (revLev F a) (dblMap F a) (fun _ hx => reverse_mem_consts hx)
        (dbl_mem_consts F)))

theorem rootPair_rev (a : ℝ) :
    rootPair F a ≫ revPair F a = revFixPair F (2 * a) ≫ rootPair F a := by
  calc rootPair F a ≫ revPair F a
      = rootPair F a ≫ revPair F a ≫ dblPair F a ≫ rootPair F a := by
        rw [dbl_root, Category.comp_id]
    _ = rootPair F a ≫ (revPair F a ≫ dblPair F a) ≫ rootPair F a := by
        simp only [Category.assoc]
    _ = rootPair F a ≫ (dblPair F a ≫ revFixPair F (2 * a)) ≫ rootPair F a := by
        rw [dblPair_rev]
    _ = (rootPair F a ≫ dblPair F a) ≫ revFixPair F (2 * a) ≫ rootPair F a := by
        simp only [Category.assoc]
    _ = revFixPair F (2 * a) ≫ rootPair F a := by
        rw [root_dbl, Category.id_comp]

/-- Pullback along doubling. -/
abbrev dblHom (a : ℝ) : InvHom (fixComplex F (2 * a)) (levComplex F a) :=
  pullHom (revPair_sq F a) (revFixPair_sq F (2 * a)) (dblPair F a) (dblPair_rev F a)

/-- Pullback along the root. -/
abbrev rootHom (a : ℝ) : InvHom (levComplex F a) (fixComplex F (2 * a)) :=
  pullHom (revFixPair_sq F (2 * a)) (revPair_sq F a) (rootPair F a) (rootPair_rev F a)

theorem root_dbl_f (a : ℝ) (j : ℕ) (x : (levComplex F a).C j) :
    (invHomComp (rootHom F a) (dblHom F a)).f j x = x := by
  have h := pull_comp_apply (dblPair F a) (rootPair F a) j x
  have h' : ((pull (dblPair F a ≫ rootPair F a)).f j).hom x = x := by
    rw [dbl_root]
    exact pull_id_apply _ j x
  exact h.symm.trans h'

theorem dbl_root_f (a : ℝ) (j : ℕ) (x : (fixComplex F (2 * a)).C j) :
    (invHomComp (dblHom F a) (rootHom F a)).f j x = x := by
  have h := pull_comp_apply (rootPair F a) (dblPair F a) j x
  have h' : ((pull (rootPair F a ≫ dblPair F a)).f j).hom x = x := by
    rw [root_dbl]
    exact pull_id_apply _ j x
  exact h.symm.trans h'

theorem HRmap_id_of {K : InvComplex} {φ : InvHom K K} (h : ∀ j x, φ.f j x = x) (q : ℕ)
    (z : HR K q) : HRmap φ q z = z := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk (bcocycleMap φ q c) = Submodule.Quotient.mk c
  congr 1
  apply Subtype.ext
  funext j
  exact h j _

/-- Doubling identifies the reflection Borel cohomology of (t_a, M) with that of the fixed pair
at level 2a. -/
def doublingEquiv (a : ℝ) (q : ℕ) :
    HR (levComplex F a) q ≃ₗ[ZMod 2] HR (fixComplex F (2 * a)) q :=
  LinearEquiv.ofLinear (HRmap (rootHom F a) q) (HRmap (dblHom F a) q)
    (LinearMap.ext fun z => by
      change HRmap (rootHom F a) q (HRmap (dblHom F a) q z) = z
      rw [← HRmap_comp]
      exact HRmap_id_of (dbl_root_f F a) q z)
    (LinearMap.ext fun z => by
      change HRmap (dblHom F a) q (HRmap (rootHom F a) q z) = z
      rw [← HRmap_comp]
      exact HRmap_id_of (root_dbl_f F a) q z)

/-- The fixed-product formula: H^J_K(X^τ_{2a} ∪ M, M) ≅ ∏_{l ≤ J} B^l_a. -/
def fixedProduct (a : ℝ) (J : ℕ) :
    HR (kFix F (2 * a)) J ≃ₗ[ZMod 2] ((l : Fin (J + 1)) → HR (levComplex F a) l) :=
  (fixedSplit F (2 * a) J).trans
    (LinearEquiv.piCongrRight fun l => (doublingEquiv F a l).symm)

theorem exists_fixedProduct (a : ℝ) (J : ℕ) :
    Nonempty (HR (kFix F (2 * a)) J ≃ₗ[ZMod 2] ((l : Fin (J + 1)) → HR (levComplex F a) l)) :=
  ⟨fixedProduct F a J⟩

end

end Finsler.BorelFixed
