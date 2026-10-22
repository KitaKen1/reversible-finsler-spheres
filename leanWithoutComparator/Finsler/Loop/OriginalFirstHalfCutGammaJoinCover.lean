module

public import Finsler.Loop.OriginalFirstHalfCutProductCochains
public import Finsler.Loop.CompactJoinCapLocalization
public import Finsler.Loop.OriginalFirstHalfJointCover

/-! An actual original-cylinder cover for cutting first. Every
nonzero gamma parent enters one genuine retained-output join carrier
on the full proper cut x Q domain, without requiring join nearness yet. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutGammaJoinCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfCutOutputJoinData
open Finsler.OriginalFirstHalfCutProductCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)

def oldCover (i : CompactRotatedCutData.source α r × Q) : Set (cutDomain α β r) :=
  (cutIso α β r).inv ⁻¹' CompactJoinCapLocalization.cover (kept α r hr) β κ i

theorem oldCover_open (i : CompactRotatedCutData.source α r × Q) : IsOpen (oldCover α β r hr κ i) :=
  (CompactJoinCapLocalization.cover_open (kept α r hr) β κ i).preimage (cutIso α β r).inv.hom.continuous

theorem exists_extension (i : CompactRotatedCutData.source α r × Q) :
    ∃ O : Set (ambient α β), IsOpen O ∧ Subtype.val ⁻¹' O = oldCover α β r hr κ i :=
  isOpen_induced_iff.mp (oldCover_open α β r hr κ i)

def extension (i : CompactRotatedCutData.source α r × Q) : Set (ambient α β) :=
  (exists_extension α β r hr κ i).choose

theorem extension_open (i : CompactRotatedCutData.source α r × Q) : IsOpen (extension α β r hr κ i) :=
  (exists_extension α β r hr κ i).choose_spec.1

theorem extension_preimage (i : CompactRotatedCutData.source α r × Q) :
    Subtype.val ⁻¹' extension α β r hr κ i = oldCover α β r hr κ i :=
  (exists_extension α β r hr κ i).choose_spec.2

def cover (ρ : ℝ) : Option (CompactRotatedCutData.source α r × Q) → Set (ambient α β) :=
  fun i => match i with
  | none => cutFar α β ρ
  | some i => extension α β r hr κ i ∩ {z | OriginalFirstHalfJointCover.cutGap α β z < r}

theorem cover_open (ρ : ℝ) (i : Option (CompactRotatedCutData.source α r × Q)) :
    IsOpen (cover α β r hr κ ρ i) := by
  cases i with
  | none => exact isOpen_lt continuous_const (OriginalFirstHalfJointCover.continuous_cutGap α β)
  | some i =>
      exact (extension_open α β r hr κ i).inter
        (isOpen_lt (OriginalFirstHalfJointCover.continuous_cutGap α β) continuous_const)

theorem cover_univ (hκ : 0 < κ) {ρ : ℝ} (hρr : ρ < r) :
    ⋃ i, cover α β r hr κ ρ i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hc : OriginalFirstHalfJointCover.cutGap α β z < r
  · let zD : cutDomain α β r := ⟨z, hc.le⟩
    let y := (cutIso α β r).inv zD
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      ((CompactJoinCapLocalization.cover_univ (kept α r hr) β hκ).symm ▸ Set.mem_univ y)
    have hi' : zD ∈ oldCover α β r hr κ i := hi
    rw [← extension_preimage α β r hr κ i] at hi'
    exact Set.mem_iUnion.mpr ⟨some i, hi', hc⟩
  · exact Set.mem_iUnion.mpr ⟨none, hρr.trans_le (le_of_not_gt hc)⟩

theorem near_image (ρ : ℝ) (i : CompactRotatedCutData.source α r × Q) :
    cover α β r hr κ ρ (some i) ⊆ originalTime α r (Q := Q) ''
      CompactJoinCapLocalization.cover (kept α r hr) β κ i := by
  intro z hz
  change z ∈ extension α β r hr κ i ∩ {z | OriginalFirstHalfJointCover.cutGap α β z < r} at hz
  let zD : cutDomain α β r := ⟨z, by
    change OriginalFirstHalfJointCover.cutGap α β z ≤ r
    exact hz.2.le⟩
  have hi : (cutIso α β r).inv zD ∈ CompactJoinCapLocalization.cover (kept α r hr) β κ i := by
    change zD ∈ oldCover α β r hr κ i
    rw [← extension_preimage α β r hr κ i]
    exact hz.1
  exact ⟨(cutIso α β r).inv zD, hi, rfl⟩

end
end Finsler.OriginalFirstHalfCutGammaJoinCover
