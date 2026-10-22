module

public import Finsler.Analysis.H1AlignmentHomotopy

/-! Genuine factorwise open covers adequate for a distance-controlled
near/far dichotomy on the whole product rectangle. A near witness controls
every point of its parent rectangle, not only the selected cap face. -/

@[expose] public section
namespace Finsler.PairDistanceCover

open Set

noncomputable section
set_option maxHeartbeats 200000

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PseudoMetricSpace E]

def cover (b : X → E) (η : ℝ) (center : X) : Set X := {x | dist (b x) (b center) < η}

theorem cover_open (b : X → E) (hb : Continuous b) (η : ℝ) (center : X) :
    IsOpen (cover b η center) :=
  isOpen_lt (hb.dist continuous_const) continuous_const

theorem cover_univ (b : X → E) {η : ℝ} (hη : 0 < η) : ⋃ center, cover b η center = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨x, by simpa only [cover, mem_ofPred_eq, dist_self] using hη⟩

theorem same_member (b : X → E) {η : ℝ} {center x x' : X}
    (hx : x ∈ cover b η center) (hx' : x' ∈ cover b η center) :
    dist (b x) (b x') < 2 * η := by
  calc
    dist (b x) (b x') ≤ dist (b x) (b center) + dist (b center) (b x') := dist_triangle _ _ _
    _ < η + η := add_lt_add hx (by
      rw [dist_comm]
      exact hx')
    _ = 2 * η := by ring

theorem witness_controls (b : X → E) (c : Y → E) {η r : ℝ}
    {center : X} {center' : Y} {x x' : X} {y y' : Y}
    (hx : x ∈ cover b η center) (hx' : x' ∈ cover b η center)
    (hy : y ∈ cover c η center') (hy' : y' ∈ cover c η center')
    (hnear : dist (b x) (c y) < r) : dist (b x') (c y') < r + 4 * η := by
  have hxx := same_member b hx' hx
  have hyy := same_member c hy hy'
  have htri := dist_triangle (b x') (b x) (c y')
  have htri' := dist_triangle (b x) (c y) (c y')
  linarith

theorem near_far_rectangle (b : X → E) (c : Y → E) (r : ℝ) (center : X) (center' : Y) :
    (∀ x ∈ cover b (r / 4) center, ∀ y ∈ cover c (r / 4) center', r ≤ dist (b x) (c y)) ∨
    (∀ x ∈ cover b (r / 4) center, ∀ y ∈ cover c (r / 4) center', dist (b x) (c y) < 2 * r) := by
  classical
  by_cases hfar : ∀ x ∈ cover b (r / 4) center, ∀ y ∈ cover c (r / 4) center',
      r ≤ dist (b x) (c y)
  · exact Or.inl hfar
  · right
    push Not at hfar
    obtain ⟨x, hx, y, hy, hxy⟩ := hfar
    intro x' hx' y' hy'
    have h := witness_controls b c hx hx' hy hy' hxy
    linarith

end
end Finsler.PairDistanceCover
