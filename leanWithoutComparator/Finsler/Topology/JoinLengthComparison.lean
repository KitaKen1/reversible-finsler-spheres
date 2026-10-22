module

public import Finsler.Topology.JoinDirectionComparison

/-! Choose the input length bounds before the join-comparison radius.
The resulting radius is uniform in the fixed join split. The homotopy has
arbitrarily small additive length cost measured against the original inputs. -/

@[expose] public section
namespace Finsler.JoinLengthComparison

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy Finsler.H1FiberBase
open Finsler.H1LoopJoin Finsler.JoinDirectionComparison Finsler.SobolevEnergy
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {n : ℕ}

theorem length_join (F : ReversibleMetric n) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (u v : SphereLoop n) (h : basepoint u = basepoint v) :
    SobolevLength.length F (join a ha0 ha1 u v h) =
      SobolevLength.length F u + SobolevLength.length F v :=
  H1PathLength.length_concat F (u.data : Space n) (v.data : Space n) ha0 ha1
    (SobolevSpherePath.sphereLoop_mem u) (SobolevSpherePath.sphereLoop_mem v)
    (end_match u v h)

theorem length_secondJoin (F : ReversibleMetric n) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (u v : SphereLoop n) :
    SobolevLength.length F (secondJoin a ha0 ha1 u v) =
      SobolevLength.length F u + SobolevLength.length F (align v (point u)) :=
  length_join F a ha0 ha1 u (align v (point u)) _

theorem length_firstJoin (F : ReversibleMetric n) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (u v : SphereLoop n) :
    SobolevLength.length F (firstJoin a ha0 ha1 u v) =
      SobolevLength.length F (align u (point v)) + SobolevLength.length F v :=
  length_join F a ha0 ha1 (align u (point v)) v _

/-- Input bounds precede both radius choices; no bound depends on the chosen tube. -/
theorem exists_bounded_input_radius (F : ReversibleMetric n) (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
      (z : nearPairs n), dist (basepoint z.val.1) (basepoint z.val.2) < ρ →
      SobolevLength.length F z.val.1 ≤ M₁ → SobolevLength.length F z.val.2 ≤ M₂ →
      ∀ s : _root_.unitInterval,
        |SobolevLength.length F (comparison a ha0 ha1 (s, z)) -
          SobolevLength.length F (secondJoin a ha0 ha1 z.val.1 z.val.2)| < ε ∧
        SobolevLength.length F (comparison a ha0 ha1 (s, z)) <
          SobolevLength.length F z.val.1 + SobolevLength.length F z.val.2 + ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hδ1, hin⟩ := exists_length_control F M₂ hM₂ hhalf
  have hM : 0 ≤ M₁ + M₂ + ε / 2 := add_nonneg (add_nonneg hM₁ hM₂) hhalf.le
  obtain ⟨ρ, hρ, hρ1, hout⟩ := exists_comparison_length_radius F (M₁ + M₂ + ε / 2) hM hhalf
  refine ⟨min δ ρ, lt_min hδ hρ, (min_le_left δ ρ).trans hδ1, ?_⟩
  intro a ha0 ha1 z hz hu hv s
  have hd : dist (point z.val.1 : Ambient n) (basepoint z.val.2) < δ :=
    hz.trans_le (min_le_left δ ρ)
  have hc := hin z.val.2 (point z.val.1) hd hv 1
  rw [hom_one] at hc
  have hinput := (abs_lt.mp hc).2
  have hj : SobolevLength.length F (secondJoin a ha0 ha1 z.val.1 z.val.2) <
      SobolevLength.length F z.val.1 + SobolevLength.length F z.val.2 + ε / 2 := by
    rw [length_secondJoin]
    linarith
  have hb : SobolevLength.length F (secondJoin a ha0 ha1 z.val.1 z.val.2) ≤
      M₁ + M₂ + ε / 2 := by linarith
  have he := hout a ha0 ha1 z (hz.trans_le (min_le_right δ ρ)) hb s
  refine ⟨he.trans (by linarith), ?_⟩
  have houtput := (abs_lt.mp he).2
  linarith

end
end Finsler.JoinLengthComparison
