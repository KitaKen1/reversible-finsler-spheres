module

public import Finsler.Loop.OriginalFirstHalfCupOneCochains
public import Finsler.Loop.EmbeddedCapOutputSupport

/-! A genuine open cover of the original time x P x Q cylinder:
join-far, self-cut-far, or a whole parent in one proper rectangle.
The actual joint proper space is homeomorphic to the old zero slice. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfJointCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.CompactH1Alignment
open Finsler.SupportedSelfCut Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)

def pairGap (z : ambient α β) : ℝ := dist (basepoint (α z.2.1)) (basepoint (β z.2.2))

def cutGap (z : ambient α β) : ℝ := distance (m + 1) (z.1, α z.2.1)

theorem continuous_pairGap : Continuous (pairGap α β) := by
  exact ((H1AlignmentHomotopy.basepoint_continuous.comp α.continuous).comp
    (continuous_fst.comp continuous_snd)).dist
      ((H1AlignmentHomotopy.basepoint_continuous.comp β.continuous).comp
        (continuous_snd.comp continuous_snd))

theorem continuous_cutGap : Continuous (cutGap α β) := by
  exact (continuous_distance (m + 1)).comp
    (continuous_fst.prodMk (α.continuous.comp (continuous_fst.comp continuous_snd)))

def proper : Set (ambient α β) := {z | pairGap α β z ≤ R ∧ cutGap α β z ≤ r}

def properHomeo : FirstInputRotatingCut.source α β R r ≃ₜ proper α β R r where
  toFun z := ⟨(z.val.1, z.val.2.val), z.val.2.property, z.property⟩
  invFun z := ⟨(z.val.1, ⟨z.val.2, z.property.1⟩), z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def properIso : TopCat.of (FirstInputRotatingCut.source α β R r) ≅ TopCat.of (proper α β R r) :=
  TopCat.isoOfHomeo (properHomeo α β R r)

def source : TopCat.of (FirstInputRotatingCut.source α β R r) ⟶ ambient α β :=
  SmallCapSubspaceLift.source (ambient α β) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (proper α β R r) (properIso α β R r)

theorem source_near : source α β R r =
    SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (FirstInputRotatingCut.source α β R r) ≫ nearSource α β R := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (η : ℝ)

def oldCover (i : FirstInputRotationCochains.space α β R r) : Set (proper α β R r) :=
  (properIso α β R r).inv ⁻¹' FirstInputRotationEndpoints.cover α β R r η 0 i

theorem oldCover_open (i : FirstInputRotationCochains.space α β R r) :
    IsOpen (oldCover α β R r η i) :=
  (FirstInputRotationEndpoints.cover_open α β R r η 0 i).preimage (properIso α β R r).inv.hom.continuous

theorem exists_extension (i : FirstInputRotationCochains.space α β R r) :
    ∃ O : Set (ambient α β), IsOpen O ∧ Subtype.val ⁻¹' O = oldCover α β R r η i :=
  isOpen_induced_iff.mp (oldCover_open α β R r η i)

def extension (i : FirstInputRotationCochains.space α β R r) : Set (ambient α β) :=
  (exists_extension α β R r η i).choose

theorem extension_open (i : FirstInputRotationCochains.space α β R r) :
    IsOpen (extension α β R r η i) :=
  (exists_extension α β R r η i).choose_spec.1

theorem extension_preimage (i : FirstInputRotationCochains.space α β R r) :
    Subtype.val ⁻¹' extension α β R r η i = oldCover α β R r η i :=
  (exists_extension α β R r η i).choose_spec.2

def cover (κ ρ : ℝ) : Option (Option (FirstInputRotationCochains.space α β R r)) → Set (ambient α β) :=
  fun i => match i with
  | none => {z | κ < pairGap α β z}
  | some none => cutFar α β ρ
  | some (some i) => extension α β R r η i ∩ {z | pairGap α β z < R} ∩ {z | cutGap α β z < r}

theorem cover_open (κ ρ : ℝ) (i : Option (Option (FirstInputRotationCochains.space α β R r))) :
    IsOpen (cover α β R r η κ ρ i) := by
  cases i with
  | none =>
    change IsOpen {z : ambient α β | κ < pairGap α β z}
    exact isOpen_lt continuous_const (continuous_pairGap α β)
  | some i =>
    cases i with
    | none => exact isOpen_lt continuous_const (continuous_cutGap α β)
    | some i =>
      exact ((extension_open α β R r η i).inter
        (isOpen_lt (continuous_pairGap α β) continuous_const)).inter
        (isOpen_lt (continuous_cutGap α β) continuous_const)

theorem cover_univ (hη : 0 < η) {κ ρ : ℝ} (hκR : κ < R) (hρr : ρ < r) :
    ⋃ i, cover α β R r η κ ρ i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hp : pairGap α β z < R
  · by_cases hc : cutGap α β z < r
    · let zB : proper α β R r := ⟨z, hp.le, hc.le⟩
      let y := (properIso α β R r).inv zB
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
        ((FirstInputRotationEndpoints.cover_univ α β R r hη 0).symm ▸ Set.mem_univ y)
      have hi' : zB ∈ oldCover α β R r η i := hi
      rw [← extension_preimage α β R r η i] at hi'
      exact Set.mem_iUnion.mpr ⟨some (some i), ⟨hi', hp⟩, hc⟩
    · exact Set.mem_iUnion.mpr ⟨some none, hρr.trans_le (le_of_not_gt hc)⟩
  · exact Set.mem_iUnion.mpr ⟨none, hκR.trans_le (le_of_not_gt hp)⟩

theorem near_image (κ ρ : ℝ) (i : FirstInputRotationCochains.space α β R r) :
    cover α β R r η κ ρ (some (some i)) ⊆
      source α β R r '' FirstInputRotationEndpoints.cover α β R r η 0 i := by
  intro z hz
  let zB : proper α β R r := ⟨z, hz.1.2.le, hz.2.le⟩
  have hi : (properIso α β R r).inv zB ∈ FirstInputRotationEndpoints.cover α β R r η 0 i := by
    change zB ∈ oldCover α β R r η i
    rw [← extension_preimage α β R r η i]
    exact hz.1.1
  refine ⟨(properIso α β R r).inv zB, hi, ?_⟩
  exact congrArg Subtype.val (ConcreteCategory.congr_hom (properIso α β R r).inv_hom_id zB)

end
end Finsler.OriginalFirstHalfJointCover
