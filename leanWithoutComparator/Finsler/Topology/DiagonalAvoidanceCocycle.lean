module

public import Finsler.Topology.CohomologyClopen
public import Finsler.Topology.DiagonalCocycle

/-! A closed actual diagonal cochain relative to the separated union of
the far set and diagonal. This proves literal diagonal endpoint vanishing;
normalization and comparison in the relative far-set group remain separate. -/

@[expose] public section
namespace Finsler.DiagonalAvoidanceCocycle

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.DiagonalGeometry Finsler.DiagonalCohomology Finsler.SphereTopClass
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

local instance (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient n) 1)

local instance (n : ℕ) : CompactSpace (product n) :=
  inferInstanceAs (CompactSpace (Sphere n × Sphere n))

local instance (n : ℕ) : T2Space (product n) :=
  inferInstanceAs (T2Space (Sphere n × Sphere n))

def diagonal (n : ℕ) : Set (product n) := {z | z.1 = z.2}

def far (n : ℕ) (ρ : ℝ) : Set (product n) :=
  {z | ρ ≤ ‖(z.2 : Ambient n) - z.1‖}

def parts (n : ℕ) (ρ : ℝ) (i : Bool) : Set (product n) :=
  if i then diagonal n else far n ρ

def avoid (n : ℕ) (ρ : ℝ) : Set (product n) := ⋃ i, parts n ρ i

def avoidancePair (n : ℕ) (ρ : ℝ) : TopPair.{0} := TopPair.ofSubset (avoid n ρ)

theorem diagonal_closed (n : ℕ) : IsClosed (diagonal n) :=
  isClosed_eq continuous_fst continuous_snd

theorem far_closed (n : ℕ) (ρ : ℝ) : IsClosed (far n ρ) :=
  isClosed_le continuous_const ((continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).norm

theorem parts_compact (n : ℕ) (ρ : ℝ) (i : Bool) : IsCompact (parts n ρ i) := by
  cases i
  · exact (far_closed n ρ).isCompact
  · exact (diagonal_closed n).isCompact

theorem parts_disjoint (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Disjoint (parts n ρ false) (parts n ρ true) := by
  apply Set.disjoint_left.mpr
  intro z hz hd
  have he : z.1 = z.2 := hd
  have h : ρ ≤ ‖(z.2 : Ambient n) - z.1‖ := hz
  rw [he, sub_self, norm_zero] at h
  linarith

def inclusion (n : ℕ) (ρ : ℝ) : TopCat.of (⋃ i, parts n ρ i) ⟶ product n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def partInclusion (n : ℕ) (ρ : ℝ) (i : Bool) : TopCat.of (parts n ρ i) ⟶ product n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem far_subset_deleted (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : far n ρ ⊆ deleted n := by
  intro z hz he
  change ρ ≤ ‖(z.2 : Ambient n) - z.1‖ at hz
  rw [he, sub_self, norm_zero] at hz
  linarith

def farToDeleted (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    TopCat.of (far n ρ) ⟶ TopCat.of (deleted n) :=
  TopCat.ofHom (ContinuousMap.inclusion (far_subset_deleted n hρ))

theorem far_restriction_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (cohPullback (partInclusion n ρ false) n).hom (ambientClass n hn) = 0 := by
  have he : partInclusion n ρ false = farToDeleted n hρ ≫ (diagonalPair n).map := by
    ext z : 1
    rfl
  have hz : (cohPullback (diagonalPair n).map n).hom (ambientClass n hn) = 0 :=
    DiagonalCohomology.restriction_zero n hn
  calc
    _ = (cohPullback (farToDeleted n hρ ≫ (diagonalPair n).map) n).hom (ambientClass n hn) :=
      congrArg (fun g : TopCat.of (parts n ρ false) ⟶ product n =>
        (cohPullback g n).hom (ambientClass n hn)) he
    _ = (cohPullback (farToDeleted n hρ) n).hom
        ((cohPullback (diagonalPair n).map n).hom (ambientClass n hn)) :=
      Cup.pullback_comp (farToDeleted n hρ) (diagonalPair n).map n (ambientClass n hn)
    _ = (cohPullback (farToDeleted n hρ) n).hom 0 :=
      congrArg (cohPullback (farToDeleted n hρ) n).hom hz
    _ = 0 := map_zero (cohPullback (farToDeleted n hρ) n).hom

theorem diagonal_restriction_zero (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ) :
    (cohPullback (partInclusion n ρ true) n).hom (ambientClass n hn) = 0 := by
  have he : partInclusion n ρ true ≫ prFirst n = partInclusion n ρ true ≫ prSecond n := by
    ext z : 1
    exact z.property
  let a := (cohPullback (partInclusion n ρ true ≫ prFirst n) n).hom (topClass n hn)
  change (cohPullback (partInclusion n ρ true) n).hom
    ((cohPullback (prFirst n) n).hom (topClass n hn) +
      (cohPullback (prSecond n) n).hom (topClass n hn)) = 0
  rw [map_add, ← Cup.pullback_comp, ← Cup.pullback_comp, ← he]
  change a + a = 0
  calc
    _ = ((1 : ZMod 2) + 1) • a := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul]

theorem restriction_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (cohPullback (inclusion n ρ) n).hom (ambientClass n hn) = 0 := by
  apply CohomologyClopen.union_eq_zero (parts n ρ) (parts_compact n ρ) (parts_disjoint n hρ) n
  intro i
  rw [← Cup.pullback_comp]
  have he : CohomologyClopen.unionInclusion (parts n ρ) i ≫ inclusion n ρ =
      partInclusion n ρ i := by
    ext z : 1
    rfl
  rw [he]
  cases i
  · exact far_restriction_zero n hn hρ
  · exact diagonal_restriction_zero n hn ρ

theorem exists_relative (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ a : (avoidancePair n ρ).singularCohomology coeff (ZMod 2) coeff n,
      (relativeToPool (avoidancePair n ρ) n).hom a = ambientClass n hn := by
  obtain ⟨a, ha⟩ := CochainComparison.relative_lift (avoidancePair n ρ) n
    (ambientClass n hn) (restriction_zero n hn hρ)
  refine ⟨a, ?_⟩
  change (cohomologyEquiv (product n) n).symm
    (((avoidancePair n ρ).singularCohomologyπ coeff (ZMod 2) coeff n).hom a) = _
  have ha' : ((avoidancePair n ρ).singularCohomologyπ coeff (ZMod 2) coeff n).hom a =
      (cohomologyEquiv (product n) n) (ambientClass n hn) := ha
  exact (congrArg (cohomologyEquiv (product n) n).symm ha').trans
    ((cohomologyEquiv (product n) n).symm_apply_apply _)

def relativeClass (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (avoidancePair n ρ).singularCohomology coeff (ZMod 2) coeff n :=
  (exists_relative n hn hρ).choose

theorem relativeClass_image (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (relativeToPool (avoidancePair n ρ) n).hom (relativeClass n hn hρ) = ambientClass n hn :=
  (exists_relative n hn hρ).choose_spec

def relativeCocycle (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.relative (avoidancePair n ρ) n :=
  CochainClass.representative (RelativeCup.cx (avoidancePair n ρ)) n (relativeClass n hn hρ)

theorem relative_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.differential (avoidancePair n ρ) n (relativeCocycle n hn hρ) = 0 :=
  CochainClass.representative_closed (RelativeCup.cx (avoidancePair n ρ)) n (relativeClass n hn hρ)

def ambientCocycle (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (product n) n :=
  RelativeCupCochain.toAmbient (avoidancePair n ρ) n (relativeCocycle n hn hρ)

theorem ambient_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (product n) n (ambientCocycle n hn hρ) = 0 :=
  RelativeCup.toAmbient_closed (avoidancePair n ρ) n (relativeCocycle n hn hρ)
    (relative_closed n hn hρ)

theorem ambient_supported (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (inclusion n ρ) n (ambientCocycle n hn hρ) = 0 :=
  RelativeCupCochain.restriction_toAmbient (avoidancePair n ρ) n (relativeCocycle n hn hρ)

theorem ambient_cocycle_class (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (cochainCxZMod2 (product n)) n (ambientCocycle n hn hρ)
      (ambient_closed n hn hρ) = ambientClass n hn := by
  have hc := CochainClass.classOf_representative (RelativeCup.cx (avoidancePair n ρ)) n
    (relativeClass n hn hρ)
  calc
    _ = (relativeToPool (avoidancePair n ρ) n).hom
        (CochainClass.classOf (RelativeCup.cx (avoidancePair n ρ)) n
          (relativeCocycle n hn hρ) (relative_closed n hn hρ)) :=
      (RelativeCup.relativeToPool_classOf (avoidancePair n ρ) n (relativeCocycle n hn hρ)
        (relative_closed n hn hρ)).symm
    _ = _ := (congrArg (relativeToPool (avoidancePair n ρ) n).hom hc).trans
      (relativeClass_image n hn hρ)

end
end Finsler.DiagonalAvoidanceCocycle
