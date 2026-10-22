module

public import Finsler.Loop.FirstInputSelfCutCochains
public import Finsler.Loop.OriginalFirstHalfNormalizedCutJoinFactor

/-! A first-input-only cut-time cover. Every relevant member lies in
one actual proper-cut output-join carrier; the remaining open is cut-far.
No tested cochain or length threshold occurs in this construction. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.FirstInputSelfCutCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)

def carrier := OriginalFirstHalfNormalizedCutJoinFactor.cutCover α r hr κ

theorem carrier_open (i : CompactRotatedCutData.source α r) : IsOpen (carrier α r hr κ i) :=
  PairDistanceCover.cover_open _ (H1AlignmentHomotopy.basepoint_continuous.comp
    (OriginalFirstHalfCutOutputJoinData.kept α r hr).continuous) _ i

theorem carrier_univ (hκ : 0 < κ) : ⋃ i, carrier α r hr κ i = Set.univ :=
  PairDistanceCover.cover_univ _ (div_pos hκ (by norm_num))

theorem exists_extension (i : CompactRotatedCutData.source α r) :
    ∃ O : Set (ambient α), IsOpen O ∧ Subtype.val ⁻¹' O = carrier α r hr κ i :=
  isOpen_induced_iff.mp (carrier_open α r hr κ i)

def extension (i : CompactRotatedCutData.source α r) : Set (ambient α) :=
  (exists_extension α r hr κ i).choose

theorem extension_open (i : CompactRotatedCutData.source α r) : IsOpen (extension α r hr κ i) :=
  (exists_extension α r hr κ i).choose_spec.1

theorem extension_preimage (i : CompactRotatedCutData.source α r) :
    Subtype.val ⁻¹' extension α r hr κ i = carrier α r hr κ i :=
  (exists_extension α r hr κ i).choose_spec.2

def cover (ρ : ℝ) : Option (CompactRotatedCutData.source α r) → Set (ambient α) :=
  fun i => match i with
  | none => far α ρ
  | some i => extension α r hr κ i ∩ {z | SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r}

theorem cover_open (ρ : ℝ) (i : Option (CompactRotatedCutData.source α r)) :
    IsOpen (cover α r hr κ ρ i) := by
  have hd : Continuous (fun z : ambient α => SupportedSelfCut.distance (m + 1) (z.1, α z.2)) :=
    (SupportedSelfCut.continuous_distance (m + 1)).comp
      (continuous_fst.prodMk (α.continuous.comp continuous_snd))
  cases i with
  | none => exact isOpen_lt continuous_const hd
  | some i => exact (extension_open α r hr κ i).inter (isOpen_lt hd continuous_const)

theorem cover_univ (hκ : 0 < κ) {ρ : ℝ} (hρr : ρ < r) :
    ⋃ i, cover α r hr κ ρ i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r
  · let zD : CompactRotatedCutData.source α r := ⟨z, hz.le⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((carrier_univ α r hr κ hκ).symm ▸ Set.mem_univ zD)
    have he : z ∈ extension α r hr κ i := by
      change zD ∈ Subtype.val ⁻¹' extension α r hr κ i
      rw [extension_preimage]
      exact hi
    exact Set.mem_iUnion.mpr ⟨some i, he, hz⟩
  · exact Set.mem_iUnion.mpr ⟨none, hρr.trans_le (le_of_not_gt hz)⟩

theorem near_image (ρ : ℝ) (i : CompactRotatedCutData.source α r) :
    cover α r hr κ ρ (some i) ⊆ source α r '' carrier α r hr κ i := by
  intro z hz
  change z ∈ extension α r hr κ i ∩ {z | SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r} at hz
  have hdist : SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r := hz.2
  let zD : CompactRotatedCutData.source α r := ⟨z, hdist.le⟩
  have hi : zD ∈ carrier α r hr κ i := by
    rw [← extension_preimage α r hr κ i]
    exact hz.1
  exact ⟨zD, hi, rfl⟩

end
end Finsler.FirstInputSelfCutCover
