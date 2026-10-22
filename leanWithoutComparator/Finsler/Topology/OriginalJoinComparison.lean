module

public import Finsler.Topology.JoinLengthComparison
public import Finsler.Topology.JoinSplitHomotopy

/-! Compare the implemented near join with the original convention:
correct the first input and give each factor half the time. The genuine
homotopy has arbitrarily small additive length loss on bounded inputs. -/

@[expose] public section
namespace Finsler.OriginalJoinComparison

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1JoinContinuity
open Finsler.JoinDirectionComparison Finsler.JoinLengthComparison
open Finsler.VariableJoinContinuity Finsler.JoinSplitHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
variable {n : ℕ}

def halfStage (a : Splits) :
    (firstMap (n := n) a a.property.1 a.property.2).Homotopy
      (firstMap half half.property.1 half.property.2) where
  toFun z := homotopy a half (z.1, firstPair z.2)
  continuous_toFun := (homotopy a half).continuous.comp
    (continuous_fst.prodMk (firstPair.continuous.comp continuous_snd))
  map_zero_left z := (homotopy a half).map_zero_left (firstPair z)
  map_one_left z := (homotopy a half).map_one_left (firstPair z)

theorem halfStage_length (F : ReversibleMetric n) (a : Splits)
    (s : _root_.unitInterval) (z : nearPairs n) :
    SobolevLength.length F (halfStage a (s, z)) =
      SobolevLength.length F (firstJoin a a.property.1 a.property.2 z.val.1 z.val.2) := by
  exact (homotopy_length F a half s (firstPair z)).trans
    (length_firstJoin F a a.property.1 a.property.2 z.val.1 z.val.2).symm

def comparisonToHalf (a : Splits) :
    (secondMap (n := n) a a.property.1 a.property.2).Homotopy
      (firstMap half half.property.1 half.property.2) :=
  (comparison a a.property.1 a.property.2).trans (halfStage a)

theorem exists_length_radius (F : ReversibleMetric n) (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ (a : Splits) (z : nearPairs n),
      dist (basepoint z.val.1) (basepoint z.val.2) < ρ →
      SobolevLength.length F z.val.1 ≤ M₁ → SobolevLength.length F z.val.2 ≤ M₂ →
      ∀ s : _root_.unitInterval, SobolevLength.length F (comparisonToHalf a (s, z)) <
        SobolevLength.length F z.val.1 + SobolevLength.length F z.val.2 + ε := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := exists_bounded_input_radius F M₁ M₂ hM₁ hM₂ hε
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro a z hz hu hv s
  change SobolevLength.length F
    (((comparison a a.property.1 a.property.2).trans (halfStage a)) (s, z)) < _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (hb a a.property.1 a.property.2 z hz hu hv _).2
  · have he : SobolevLength.length F
        (firstJoin a a.property.1 a.property.2 z.val.1 z.val.2) <
        SobolevLength.length F z.val.1 + SobolevLength.length F z.val.2 + ε := by
      have hlast := (hb a a.property.1 a.property.2 z hz hu hv 1).2
      have hend : comparison a a.property.1 a.property.2 (1, z) =
          firstJoin a a.property.1 a.property.2 z.val.1 z.val.2 :=
        (comparison a a.property.1 a.property.2).map_one_left z
      exact (congrArg (SobolevLength.length F) hend).symm.trans_lt hlast
    exact (halfStage_length F a _ z).trans_lt he

end
end Finsler.OriginalJoinComparison
