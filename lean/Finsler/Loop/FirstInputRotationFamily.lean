module

public import Finsler.Loop.CompactNearJoinParameters
public import Finsler.Loop.OrthogonalSelfCutDistance
public import Finsler.Topology.UniformSelfCutCollar
public import Finsler.Topology.AnnularSelfCut

/-! The actual partial correction of the original first loop on a
compact near-pair source. Its full cut cylinder preserves cut distance
and both endpoint collars. A single tube controls the length of every
intermediate loop before all tested cochains and degrees. -/

@[expose] public section
namespace Finsler.FirstInputRotationFamily

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.H1FiberBase Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy
open Finsler.H1OrthogonalLength Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R < 1)

def nearData (hR : R < 1) : C(CompactNearJoinParameters.tube α β R, H1AlignmentHomotopy.nearLoops n) := by
  let f : C(CompactNearJoinParameters.tube α β R, SphereLoop n) :=
    ⟨fun z => α z.val.1, α.continuous.comp (continuous_fst.comp continuous_subtype_val)⟩
  let g : C(CompactNearJoinParameters.tube α β R, Sphere n) :=
    ⟨fun z => point (β z.val.2), continuous_point.comp (β.continuous.comp (continuous_snd.comp continuous_subtype_val))⟩
  have hn (z : CompactNearJoinParameters.tube α β R) : (f z, g z) ∈ H1AlignmentHomotopy.nearLoops n := by
    change dist (basepoint (β z.val.2)) (basepoint (α z.val.1)) < 1
    rw [dist_comm]
    exact z.property.trans_lt hR
  exact ⟨fun z => ⟨(f z, g z), hn z⟩, (f.continuous.prodMk g.continuous).subtype_mk hn⟩

def family (hR : R < 1) : C(_root_.unitInterval × CompactNearJoinParameters.tube α β R, SphereLoop n) :=
  (H1AlignmentHomotopy.alignmentHomotopy (n := n)).toContinuousMap.comp
    (show C(_root_.unitInterval × CompactNearJoinParameters.tube α β R,
      _root_.unitInterval × H1AlignmentHomotopy.nearLoops n) from
      ⟨fun z => (z.1, nearData α β R hR z.2),
        continuous_fst.prodMk ((nearData α β R hR).continuous.comp continuous_snd)⟩)

theorem family_zero (z : CompactNearJoinParameters.tube α β R) :
    family α β R hR (0, z) = α z.val.1 :=
  H1AlignmentHomotopy.hom_zero _ _

theorem family_one (z : CompactNearJoinParameters.tube α β R) :
    family α β R hR (1, z) = (CompactNearJoinParameters.inputs α β R hR z).val.1 :=
  H1AlignmentHomotopy.hom_one _ _

def timeFamily (hR : R < 1) : TopCat.of (ClosedInterval × (_root_.unitInterval × CompactNearJoinParameters.tube α β R)) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (z.1, family α β R hR z.2),
    continuous_fst.prodMk ((family α β R hR).continuous.comp continuous_snd)⟩

theorem time_distance (t : ClosedInterval) (s : _root_.unitInterval) (z : CompactNearJoinParameters.tube α β R) :
    distance n (timeFamily α β R hR (t, (s, z))) = distance n (t, α z.val.1) := by
  change distance n (t, rotateLoop (RotorHomotopy.path s (basepoint (α z.val.1)) (point (β z.val.2))) (α z.val.1)) = _
  exact OrthogonalSelfCutDistance.distance _ _ _

theorem distance_zero (s : _root_.unitInterval) (z : CompactNearJoinParameters.tube α β R) :
    distance n (timeFamily α β R hR (0, (s, z))) = 0 :=
  (time_distance α β R hR 0 s z).trans (UniformSelfCutCollar.distance_zero α z.val.1)

theorem distance_one (s : _root_.unitInterval) (z : CompactNearJoinParameters.tube α β R) :
    distance n (timeFamily α β R hR (1, (s, z))) = 0 :=
  (time_distance α β R hR 1 s z).trans (UniformSelfCutCollar.distance_one α z.val.1)

def collar (δ : ℝ) : Set (ClosedInterval × (_root_.unitInterval × CompactNearJoinParameters.tube α β R)) :=
  {z | distance n (z.1, α z.2.2.val.1) ≤ δ}

theorem annular_inner_zero (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap
      (TopCat.of (ClosedInterval × (_root_.unitInterval × CompactNearJoinParameters.tube α β R)))
      (collar α β R δ)) n
      (cochainPullback (timeFamily α β R hR) n (AnnularSelfCut.cocycle n hn h)) = 0 := by
  apply pullback_support (timeFamily α β R hR) (collar α β R δ) {z | distance n z ≤ δ}
    _ n (AnnularSelfCut.cocycle n hn h) (AnnularSelfCut.cocycle_small_zero n hn h)
  intro z hz
  change distance n (timeFamily α β R hR z) ≤ δ
  rw [time_distance]
  exact hz

theorem exists_length_control [CompactSpace P] (F : ReversibleMetric n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∃ hR : R < 1, ∀ (s : _root_.unitInterval) (z : CompactNearJoinParameters.tube α β R),
      |SobolevLength.length F (family α β R hR (s, z)) - SobolevLength.length F (α z.val.1)| < ε := by
  obtain ⟨M, hM, hbound, ρ, hρ, hρ1, hcontrol⟩ := H1AlignmentHomotopy.exists_compact_control F
    (K := Set.univ) isCompact_univ α α.continuous.continuousOn hε
  let R : ℝ := min (ρ / 2) (1 / 2)
  have hR : 0 < R := lt_min (half_pos hρ) (by norm_num)
  have hR1 : R < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hRρ : R < ρ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨R, hR, hR1, ?_⟩
  intro s z
  exact hcontrol z.val.1 (Set.mem_univ _) (point (β z.val.2))
    (by
      change dist (basepoint (β z.val.2)) (basepoint (α z.val.1)) < ρ
      rw [dist_comm]
      exact z.property.trans_lt hRρ) s

end
end Finsler.FirstInputRotationFamily
