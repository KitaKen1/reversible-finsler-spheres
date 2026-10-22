module

public import Finsler.Topology.OriginalSecondHalfFamily
public import Finsler.Topology.JoinLengthComparison

/-! The genuine compact near-pair tube and total joined-loop length
bound for the original first-input correction. The input length bound is
chosen before the correction radius. The radius precedes all cochains,
degrees and retained-length thresholds. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfCompactTube

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.JoinDirectionComparison Finsler.JoinLengthComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}

def tube (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) :
    Set (P × (ClosedInterval × Q)) :=
  {z | dist (basepoint (α z.1)) (basepoint (β z.2.2)) ≤ R}

theorem compact [CompactSpace P] [CompactSpace Q]
    (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) :
    IsCompact (tube α β R) := by
  apply IsClosed.isCompact
  exact isClosed_le
    ((H1AlignmentHomotopy.basepoint_continuous.comp (α.continuous.comp continuous_fst)).dist
      (H1AlignmentHomotopy.basepoint_continuous.comp
        (β.continuous.comp (continuous_snd.comp continuous_snd)))) continuous_const

theorem near (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R < 1)
    (z : tube α β R) :
    dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1 :=
  z.property.trans_lt hR

theorem contains_near (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
    {R ρJ : ℝ} (h : 2 * ρJ ≤ R) (z : P × (ClosedInterval × Q))
    (hz : dist (basepoint (α z.1)) (basepoint (β z.2.2)) < 2 * ρJ) : z ∈ tube α β R :=
  hz.le.trans h

theorem exists_length_tube [CompactSpace P]
    (F : ReversibleMetric n) (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∃ hR : R < 1, ∀ z : tube α β R,
      SobolevLength.length F
        (OriginalSecondHalfFamily.family α β (tube α β R) (near α β R hR) z).2 <
        SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2.2) + ε := by
  obtain ⟨M, hM, hbound, ρ, hρ, halign⟩ := CompactH1Alignment.exists_family_alignment F
    (K := Set.univ) isCompact_univ α α.continuous.continuousOn hε
  let R := min (ρ / 2) (1 / 2)
  have hR : 0 < R := lt_min (half_pos hρ) (by norm_num)
  have hR1 : R < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hRρ : R < ρ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨R, hR, hR1, ?_⟩
  intro z
  have hd : dist (H1FiberBase.point (β z.val.2.2) : Ambient n) (basepoint (α z.val.1)) < ρ := by
    change dist (basepoint (β z.val.2.2)) (basepoint (α z.val.1)) < ρ
    rw [dist_comm]
    exact z.property.trans_lt hRρ
  have hl := (abs_lt.mp (halign z.val.1 (Set.mem_univ _) (H1FiberBase.point (β z.val.2.2)) hd).2).2
  change SobolevLength.length F
    (firstJoin (1 / 2) (by norm_num) (by norm_num) (α z.val.1) (β z.val.2.2)) < _
  rw [length_firstJoin]
  linarith

end
end Finsler.OriginalSecondHalfCompactTube
