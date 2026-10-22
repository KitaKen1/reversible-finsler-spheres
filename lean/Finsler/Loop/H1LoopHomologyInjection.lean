module

public import Finsler.Loop.CompactMapZeroFactor
public import Finsler.Loop.H1PolygonReplacementHomotopy
public import Finsler.Loop.ContinuousLoopHomologySurjection
public import Finsler.Analysis.IntervalH1EnergyContinuity

/-! The genuine strong-H1 to ordinary continuous-loop homology map is
injective. A null class is detected on one compact ordinary family;
the literal polygon replacement on that family agrees on the original
compact H1 family with the endpoint of the genuine Milnor homotopy. -/

@[expose] public section
namespace Finsler.H1LoopHomologyInjection
open CategoryTheory AlgebraicTopology Topology TopologicalSpace
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1500000

theorem compact_energy_bound {n : ℕ} (F : ReversibleMetric n) (K : Compacts (Loops n)) :
    ∃ a : ℝ, ∀ u : K, SobolevEnergy.energy F u.val < a ^ 2 := by
  obtain ⟨B, hB⟩ := K.isCompact.exists_bound_of_continuousOn
    (SobolevEnergy.energy_continuous F).continuousOn
  refine ⟨|B| + 1, fun u => ?_⟩
  have hb := hB u.val u.property
  have he : SobolevEnergy.energy F u.val ≤ B := (le_abs_self _).trans hb
  nlinarith [abs_nonneg B, le_abs_self B, sq_nonneg (|B|)]

theorem kernel_zero (n q : ℕ) (z : (chains (Loops n)).homology q)
    (hz : (HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom z = 0) :
    z = 0 := by
  obtain ⟨K, y, hy⟩ := CompactHomologyLift.exists_lift (Loops n) q z
  let u := SupportedCap.subspaceMap (Loops n) (K : Set (Loops n))
  have hKy : (HomologicalComplex.homologyMap (push (u ≫ ContinuousLoopModel.inclusion n)) q).hom y = 0 := by
    rw [push_comp, HomologicalComplex.homologyMap_comp]
    change (HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom
      ((HomologicalComplex.homologyMap (push u) q).hom y) = 0
    rw [hy]
    exact hz
  obtain ⟨L, g, hg, hzero⟩ := CompactMapZeroFactor.exists_factor
    (ContinuousLoopModel.inclusion n) K q y hKy
  let F := Geometry.roundMetric n
  obtain ⟨S⟩ := PolygonModel.exists_segmentData F
  obtain ⟨a, hE⟩ := compact_energy_bound F K
  obtain ⟨Ne, he⟩ := PolygonSampling.exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨Nc, hc, hs⟩ := CompactContinuousLoopSampling.exists_short_samples L S.pos
  let N := max Ne Nc
  have hN : 0 < N := hc.trans_le (le_max_right _ _)
  let : NeZero N := ⟨hN.ne'⟩
  let M : PolygonModelData F a N := PolygonModelData.mk S (he N (le_max_left _ _) hN)
  have hshort : ∀ v : L, PolygonLoop.ShortPolygon M.δ (CompactContinuousLoopSampling.sample N v.val) :=
    hs N (le_max_right _ _)
  have hh := H1PolygonReplacementHomotopy.homology M u hE L hshort g hg q
  rw [← hy, hh, push_comp, HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap
    (push (CompactContinuousLoopPolygon.approximation M.toSegmentData L N hshort)) q).hom
      ((HomologicalComplex.homologyMap (push g) q).hom y) = 0
  rw [hzero, map_zero]

theorem homology_injective (n q : ℕ) : Function.Injective
    (HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom := by
  intro a b h
  apply sub_eq_zero.mp
  apply kernel_zero n q (a - b)
  rw [map_sub, h, sub_self]

end
end Finsler.H1LoopHomologyInjection
