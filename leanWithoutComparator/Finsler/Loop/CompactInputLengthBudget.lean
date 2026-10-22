module

public import Finsler.Analysis.SelfCutOscillation
public import Mathlib.Topology.Order.Compact

/-! Split a coupled compact input budget into two strict sublevels
with a strict remaining margin. Empty parameter spaces are included.
This supplies actual separate length thresholds for composing the
canonical self-cut operation with a filtered bilinear loop product. -/

@[expose] public section
namespace Finsler.CompactInputLengthBudget

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev

set_option autoImplicit false

theorem split {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q] {f : P → ℝ} {g : Q → ℝ}
    (hf : Continuous f) (hg : Continuous g) {A : ℝ}
    (hA : ∀ x y, f x + g y < A) :
    ∃ a b : ℝ, (∀ x, f x < a) ∧ (∀ y, g y < b) ∧ a + b < A := by
  classical
  by_cases hP : Nonempty P
  · obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn (⟨Classical.choice hP, Set.mem_univ _⟩ : (Set.univ : Set P).Nonempty)
      hf.continuousOn
    by_cases hQ : Nonempty Q
    · obtain ⟨y, _, hy⟩ := isCompact_univ.exists_isMaxOn (⟨Classical.choice hQ, Set.mem_univ _⟩ : (Set.univ : Set Q).Nonempty)
        hg.continuousOn
      refine ⟨f x + (A - f x - g y) / 3, g y + (A - f x - g y) / 3, ?_, ?_, ?_⟩
      · intro z
        have hmax : f z ≤ f x := hx (Set.mem_univ z)
        have hgap := hA x y
        linarith
      · intro z
        have hmax : g z ≤ g y := hy (Set.mem_univ z)
        have hgap := hA x y
        linarith
      · have hgap := hA x y
        linarith
    · refine ⟨f x + 1, A - f x - 2, ?_, ?_, ?_⟩
      · intro z
        have hmax : f z ≤ f x := hx (Set.mem_univ z)
        linarith
      · intro z
        exact False.elim (hQ ⟨z⟩)
      · linarith
  · obtain ⟨c, hc⟩ := (isCompact_range hg).bddAbove
    refine ⟨A - c - 2, c + 1, ?_, ?_, ?_⟩
    · intro z
      exact False.elim (hP ⟨z⟩)
    · intro z
      have hz : g z ≤ c := hc (Set.mem_range_self z)
      linarith
    · linarith

theorem loop_lengths {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q] {n : ℕ}
    (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (F : ReversibleMetric n)
    {A : ℝ} (hA : ∀ x y, SobolevLength.length F (α x) + SobolevLength.length F (β y) < A) :
    ∃ a b : ℝ, (∀ x, SobolevLength.length F (α x) < a) ∧
      (∀ y, SobolevLength.length F (β y) < b) ∧ a + b < A :=
  split ((SelfCutOscillation.continuous_length F).comp α.continuous)
    ((SelfCutOscillation.continuous_length F).comp β.continuous) hA

theorem output_margin {a b A L ε : ℝ} (hab : a + b < A) (hε : 0 < ε) :
    (a - L + 3 * ε) + b + ε < A - L + 5 * ε := by
  linarith

end Finsler.CompactInputLengthBudget

