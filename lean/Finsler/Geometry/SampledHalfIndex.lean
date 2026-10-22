module

public import Finsler.Geometry.FixedIterateIndex
public import Finsler.Geometry.GeodesicNormalData

/-! Fixed crossing support and sampled half-index comparisons. -/

@[expose] public section

namespace Finsler.SampledHalfIndex

open Module QuadraticMap QuadraticForm Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty
open Finsler.AmbientHessian Finsler.SymmetricBlocks Finsler.AmbientNormalIndex
open Finsler.GeodesicFrames Finsler.CircleFrameField Finsler.PolygonIterateReduction
open Finsler.AmbientSymmetry Finsler.AmbientRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5

variable {n : ℕ} {F : ReversibleMetric n}

theorem exists_half_index (g : Finsler.Geodesics.ClosedGeodesic F) (j : ℕ) [NeZero j] :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N], ∀ a : ℝ,
      sigNeg ((sndQuad (pen F (2 * (j * (2 * N))) 1)
        (amb (iterate 2 (j * (2 * N)) (rootFamily g j N a)))).restrict
          (fixed (rotL (n := n) 2 (j * (2 * N))))) = (iterData g).I j := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_ambientMinEnergy_contDiffAt F
  obtain ⟨N₀, hN₀⟩ := (iterData g).data δ hδpos
  refine ⟨N₀, fun N hN _ a => ?_⟩
  have hfacts : SampleData g (iterData g).I (iterData g).ν (iterData g).L δ N a := hN₀ N hN a
  have hq : ShortPolygon δ (rootFamily g j N a) := shortPolygon_iterate j (2 * N) hfacts.1
  have hne : ∀ i, rootFamily g j N a (i + 1) ≠ rootFamily g j N a i :=
    iterate_ne j (2 * N) hfacts.2.1
  have hc : PolyCritical F (j * (2 * N)) (rootFamily g j N a) :=
    polyCritical_iterate j F hδ hfacts.1 hfacts.2.1 hfacts.2.2.1
  have hs := hessian_isSymmetric F hδ hq hne
  have hidx : index F (rootFamily g j N a) hs = (iterData g).I j :=
    (hfacts.2.2.2.1 j).2 hs
  have hreg : ContDiffAt ℝ 2 (pen F (2 * (j * (2 * N))) 1)
      (amb (iterate 2 (j * (2 * N)) (rootFamily g j N a))) :=
    (pen_contDiffAt_three F hδ (shortPolygon_iterate 2 (j * (2 * N)) hq)
      (iterate_ne 2 (j * (2 * N)) hne) 1).of_le (by norm_num)
  exact (FixedIterateIndex.sigNeg_fixed_pen_index 2 (j * (2 * N)) F hδ
    (rootFamily g j N a) hq hne hc zero_le_one hreg hs).trans hidx

end

end Finsler.SampledHalfIndex
