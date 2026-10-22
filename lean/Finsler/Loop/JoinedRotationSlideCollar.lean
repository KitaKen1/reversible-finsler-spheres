module

public import Finsler.Loop.OriginalPairSlideCollar
public import Finsler.Loop.FirstInputRotationTimeTrim
public import Finsler.Topology.JoinedFamilyNaturality

/-! The same original-pair collar controls all actual rotation sides
and all four joined first/second-half slide sides, before every later
near-pair tube. The first correction preserves the exact cut distance. -/

@[expose] public section
namespace Finsler.JoinedRotationSlideCollar

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.FirstInputRotationCutCylinder Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R ≤ 1 / 2)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

local instance : CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

theorem first_distance (z : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    distance n (JoinedFamilyNaturality.globalMap
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 1 z) =
      distance n (InteriorTimeSlide.slide a ha.le ha1.le z.1, α z.2.val.1) := by
  change distance n (JoinedHalfCollars.first
    (InteriorTimeSlide.slide a ha.le ha1.le z.1,
      CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z.2)) = _
  rw [JoinedHalfCollars.first_distance]
  have hd := FirstInputRotationFamily.time_distance α β R (hR.trans_lt (by norm_num))
    (InteriorTimeSlide.slide a ha.le ha1.le z.1) 1 z.2
  change distance n (InteriorTimeSlide.slide a ha.le ha1.le z.1,
    FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num)) (1, z.2)) = _ at hd
  rw [FirstInputRotationFamily.family_one] at hd
  exact hd

theorem second_distance (z : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    distance n (JoinedFamilyNaturality.globalMap
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 2 z) =
      distance n (InteriorTimeSlide.slide a ha.le ha1.le z.1, β z.2.val.2) := by
  change distance n (JoinedHalfCollars.second
    (InteriorTimeSlide.slide a ha.le ha1.le z.1,
      CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z.2)) = _
  rw [JoinedHalfCollars.second_distance]
  rfl

theorem exists_uniform {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      ∀ (R : ℝ) (hR : R ≤ 1 / 2),
      (∀ (s : _root_.unitInterval) (x : input α β R),
        sideHomotopy α β R a ha ha1 0 (s, x) ∈ collar α β R δ) ∧
      (∀ (s : _root_.unitInterval) (x : input α β R),
        sideHomotopy α β R a ha ha1 1 (s, x) ∈ collar α β R δ) ∧
      (∀ (i : Fin 2) (s : ClosedInterval) (x : CompactNearJoinParameters.tube α β R),
        distance n (JoinedFamilyNaturality.globalMap
          (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
            a ha.le ha1.le i.succ ((s, 0), x)) ≤ δ) ∧
      (∀ (i : Fin 2) (s : ClosedInterval) (x : CompactNearJoinParameters.tube α β R),
        distance n (JoinedFamilyNaturality.globalMap
          (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
            a ha.le ha1.le i.succ ((s, 1), x)) ≤ δ) := by
  obtain ⟨a, ha, ha1, hα₀, hα₁, hβ₀, hβ₁⟩ := OriginalPairSlideCollar.exists_pair α β hδ
  refine ⟨a, ha, ha1, ?_⟩
  intro R hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s x
    exact hα₀ s x.2.val.1
  · intro s x
    exact hα₁ s x.2.val.1
  · intro i s x
    fin_cases i
    · change distance n (JoinedFamilyNaturality.globalMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
          a ha.le ha1.le 1 ((s, 0), x)) ≤ δ
      rw [first_distance α β R hR a ha ha1]
      exact hα₀ s x.val.1
    · change distance n (JoinedFamilyNaturality.globalMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
          a ha.le ha1.le 2 ((s, 0), x)) ≤ δ
      rw [second_distance α β R hR a ha ha1]
      exact hβ₀ s x.val.2
  · intro i s x
    fin_cases i
    · change distance n (JoinedFamilyNaturality.globalMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
          a ha.le ha1.le 1 ((s, 1), x)) ≤ δ
      rw [first_distance α β R hR a ha ha1]
      exact hα₁ s x.val.1
    · change distance n (JoinedFamilyNaturality.globalMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
          a ha.le ha1.le 2 ((s, 1), x)) ≤ δ
      rw [second_distance α β R hR a ha ha1]
      exact hβ₁ s x.val.2

end
end Finsler.JoinedRotationSlideCollar
