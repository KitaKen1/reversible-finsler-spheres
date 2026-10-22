module

public import Finsler.Loop.OriginalFirstHalfZeroCover
public import Finsler.Loop.SmallCapSubspaceLift

/-! A real original time-cylinder cover for the first spatial join cap.
The near pieces land in the actual zero-cylinder gamma cover. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfJoinTimeCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)

def pairDomain : Set (ambient α β) := {z | OriginalFirstHalfJointCover.pairGap α β z ≤ R}

def pairHomeo : OriginalFirstHalfZeroCover.space α β R ≃ₜ pairDomain α β R where
  toFun z := ⟨(z.1, z.2.val), z.2.property⟩
  invFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def pairIso : OriginalFirstHalfZeroCover.space α β R ≅ TopCat.of (pairDomain α β R) :=
  TopCat.isoOfHomeo (pairHomeo α β R)

theorem source_eq : SmallCapSubspaceLift.source (ambient α β)
    (OriginalFirstHalfZeroCover.space α β R) (pairDomain α β R) (pairIso α β R) = nearSource α β R := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (η ρ : ℝ)

def oldCover (i : Option (FirstInputRotationCochains.space α β R r)) : Set (pairDomain α β R) :=
  (pairIso α β R).inv ⁻¹' OriginalFirstHalfZeroCover.cover α β R r η ρ i

theorem oldCover_open (i : Option (FirstInputRotationCochains.space α β R r)) :
    IsOpen (oldCover α β R r η ρ i) :=
  (OriginalFirstHalfZeroCover.cover_open α β R r η ρ i).preimage (pairIso α β R).inv.hom.continuous

theorem exists_extension (i : Option (FirstInputRotationCochains.space α β R r)) :
    ∃ O : Set (ambient α β), IsOpen O ∧ Subtype.val ⁻¹' O = oldCover α β R r η ρ i :=
  isOpen_induced_iff.mp (oldCover_open α β R r η ρ i)

def extension (i : Option (FirstInputRotationCochains.space α β R r)) : Set (ambient α β) :=
  (exists_extension α β R r η ρ i).choose

theorem extension_open (i : Option (FirstInputRotationCochains.space α β R r)) :
    IsOpen (extension α β R r η ρ i) :=
  (exists_extension α β R r η ρ i).choose_spec.1

theorem extension_preimage (i : Option (FirstInputRotationCochains.space α β R r)) :
    Subtype.val ⁻¹' extension α β R r η ρ i = oldCover α β R r η ρ i :=
  (exists_extension α β R r η ρ i).choose_spec.2

def cover (κ : ℝ) : Option (Option (FirstInputRotationCochains.space α β R r)) → Set (ambient α β) :=
  fun i => match i with
  | none => {z | κ < OriginalFirstHalfJointCover.pairGap α β z}
  | some i => extension α β R r η ρ i ∩ {z | OriginalFirstHalfJointCover.pairGap α β z < R}

theorem cover_open (κ : ℝ) (i : Option (Option (FirstInputRotationCochains.space α β R r))) :
    IsOpen (cover α β R r η ρ κ i) := by
  cases i with
  | none => exact isOpen_lt continuous_const (OriginalFirstHalfJointCover.continuous_pairGap α β)
  | some i =>
      exact (extension_open α β R r η ρ i).inter
        (isOpen_lt (OriginalFirstHalfJointCover.continuous_pairGap α β) continuous_const)

theorem cover_univ (hη : 0 < η) {κ : ℝ} (hκR : κ < R) (hρr : ρ < r) :
    ⋃ i, cover α β R r η ρ κ i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hp : OriginalFirstHalfJointCover.pairGap α β z < R
  · let zB : pairDomain α β R := ⟨z, hp.le⟩
    let y := (pairIso α β R).inv zB
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      ((OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr).symm ▸ Set.mem_univ y)
    have hi' : zB ∈ oldCover α β R r η ρ i := hi
    rw [← extension_preimage α β R r η ρ i] at hi'
    exact Set.mem_iUnion.mpr ⟨some i, hi', hp⟩
  · exact Set.mem_iUnion.mpr ⟨none, hκR.trans_le (le_of_not_gt hp)⟩

theorem near_image (κ : ℝ) (i : Option (FirstInputRotationCochains.space α β R r)) :
    cover α β R r η ρ κ (some i) ⊆
      nearSource α β R '' OriginalFirstHalfZeroCover.cover α β R r η ρ i := by
  intro z hz
  change z ∈ extension α β R r η ρ i ∩ {z | OriginalFirstHalfJointCover.pairGap α β z < R} at hz
  let zB : pairDomain α β R := ⟨z, by
    change OriginalFirstHalfJointCover.pairGap α β z ≤ R
    exact hz.2.le⟩
  have hi : (pairIso α β R).inv zB ∈ OriginalFirstHalfZeroCover.cover α β R r η ρ i := by
    change zB ∈ oldCover α β R r η ρ i
    rw [← extension_preimage α β R r η ρ i]
    exact hz.1
  refine ⟨(pairIso α β R).inv zB, hi, ?_⟩
  rfl

end
end Finsler.OriginalFirstHalfJoinTimeCover
