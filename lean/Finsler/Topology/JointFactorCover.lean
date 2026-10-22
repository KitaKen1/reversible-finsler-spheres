module

public import Finsler.Topology.PairDistanceCover

/-! Actual open full factor covers simultaneously controlling the
original parameter distance and the join basepoint distance. -/

@[expose] public section
namespace Finsler.JointFactorCover

noncomputable section
set_option autoImplicit false

variable {X E : Type*} [PseudoMetricSpace X] [PseudoMetricSpace E]

def cover (b : X → E) (η ρ : ℝ) (center : X) : Set X :=
  PairDistanceCover.cover id η center ∩ PairDistanceCover.cover b (ρ / 4) center

theorem isOpen (b : X → E) (hb : Continuous b) (η ρ : ℝ) (center : X) :
    IsOpen (cover b η ρ center) :=
  (PairDistanceCover.cover_open id continuous_id η center).inter
    (PairDistanceCover.cover_open b hb (ρ / 4) center)

theorem covers (b : X → E) {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ⋃ center, cover b η ρ center = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨x, ?_, ?_⟩
  · change dist x x < η
    simpa only [dist_self] using hη
  · change dist (b x) (b x) < ρ / 4
    simpa only [dist_self] using div_pos hρ (by norm_num : (0 : ℝ) < 4)

theorem mono (b : X → E) {η ζ : ℝ} (h : η ≤ ζ) (ρ : ℝ) (center : X) :
    cover b η ρ center ⊆ cover b ζ ρ center := by
  intro x hx
  exact ⟨hx.1.trans_le h, hx.2⟩

end
end Finsler.JointFactorCover
