module

public import Finsler.Geometry.CircleFixedIndex
public import Finsler.Geometry.FixedHessianIndex

/-! The actual signed frame shift on an even critical circle lies between the
half-iterate index minus the root index and the half-iterate index itself. -/

@[expose] public section

namespace Finsler.CircleFixedShift

open Module QuadraticForm QuadraticMap Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty
open Finsler.AmbientNormalIndex Finsler.AmbientRotation Finsler.SymmetricBlocks
open Finsler.GeodesicFrames Finsler.CircleFrameField Finsler.CircleHalfRotation
open Finsler.PolygonIterateReduction Finsler.DefiniteFrames Finsler.CurveEquivFrames

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_shift_bounds {n : ℕ} {F : ReversibleMetric n}
    (g : Finsler.Geodesics.ClosedGeodesic F) (m s j : ℕ) [NeZero m] [NeZero s] [NeZero j]
    (hms : m * s = 2 * j) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {b p : ℕ}
      (S₁ : SignedFrameField g s m N 1 b) (_S₂ : SignedFrameField g s m N (-1) p)
      (_ψ : normal (rotL (n := n) m (s * (2 * N))) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ)),
        Fintype.card {i : Fin b // S₁.d i = 1} ≤ (iterData g).I j ∧
          (iterData g).I j ≤ (iterData g).I s + Fintype.card {i : Fin b // S₁.d i = 1} := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_ambientMinEnergy_contDiffAt F
  obtain ⟨N₁, hN₁⟩ := (iterData g).data δ hδpos
  obtain ⟨N₂, hN₂⟩ := CircleFixedIndex.exists_even_half_index g m s j hms
  refine ⟨max N₁ N₂, fun N hN _ b p S₁ S₂ ψ => ?_⟩
  let a : ℝ := 0
  have hfacts : SampleData g (iterData g).I (iterData g).ν (iterData g).L δ N a :=
    hN₁ N ((le_max_left _ _).trans hN) a
  have hq : ShortPolygon δ (rootFamily g s N a) := shortPolygon_iterate s (2 * N) hfacts.1
  have hne : ∀ i, rootFamily g s N a (i + 1) ≠ rootFamily g s N a i :=
    iterate_ne s (2 * N) hfacts.2.1
  have hc : PolyCritical F (s * (2 * N)) (rootFamily g s N a) :=
    polyCritical_iterate s F hδ hfacts.1 hfacts.2.1 hfacts.2.2.1
  have hs := hessian_isSymmetric F hδ hq hne
  have hidx : index F (rootFamily g s N a) hs = (iterData g).I s := (hfacts.2.2.2.1 s).2 hs
  have hreg3 : ContDiffAt ℝ 3 (pen F (m * (s * (2 * N))) 1)
      (amb (iterate m (s * (2 * N)) (rootFamily g s N a))) :=
    S₁.subset_smooth (S₁.circle_mem a)
  have hreg := hreg3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hn : Neg (normalForm m (s * (2 * N)) F (amb (rootFamily g s N a)))
      (S₁.G (amb (rootFamily g s N a))) := by
    simpa only [one_smul] using S₁.definite _ (S₁.circle_mem a)
  have hp : Neg (-normalForm m (s * (2 * N)) F (amb (rootFamily g s N a)))
      (S₂.G (amb (rootFamily g s N a))) := by
    simpa only [neg_one_smul] using S₂.definite _ (S₂.circle_mem a)
  have heven : Even (m * s) := ⟨j, by omega⟩
  have h := FixedHessianIndex.fixed_shift_bounds m (s * (2 * N)) S₁.G S₂.G ψ F hδ
    (rootFamily g s N a) hq hne hc hreg hs hn hp (halfIndex m s N)
    (root_half_even g m s N heven a) S₁.d S₂.d S₁.signs S₂.signs
    (fun i => congrFun (S₁.equivariant (amb (rootFamily g s N a))) i)
    (fun i => congrFun (S₂.equivariant (amb (rootFamily g s N a))) i)
  rw [hN₂ N ((le_max_right _ _).trans hN) a, hidx] at h
  exact h

end

end Finsler.CircleFixedShift
