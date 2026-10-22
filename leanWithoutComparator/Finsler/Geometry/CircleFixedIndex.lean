module

public import Finsler.Geometry.SampledHalfIndex
public import Finsler.Geometry.CircleHalfRotation

/-! Identify the half-fixed Hessian index on the actual grouped polygon used by the
signed frame chart. Equal vertex counts are transported explicitly; equality of the
grouped iterates is checked on natural-number representatives. -/

@[expose] public section

namespace Finsler.CircleFixedIndex

open Module QuadraticForm QuadraticMap
open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientSymmetry Finsler.SymmetricBlocks Finsler.AmbientNormalIndex
open Finsler.AmbientPenalty Finsler.AmbientHessian Finsler.PolygonLoop
open Finsler.GeodesicFrames Finsler.CircleFrameField Finsler.CircleHalfRotation
open Finsler.PolygonSampling Finsler.SmoothSobolev
open Finsler.PolygonDescent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def reindex {K L : ℕ} {α : Type*} (h : K = L) (q : ZMod K → α) : ZMod L → α := h ▸ q

theorem reindex_natCast {K L : ℕ} {α : Type*} (h : K = L) (q : ZMod K → α) (t : ℕ) :
    reindex h q (t : ZMod L) = q (t : ZMod K) := by
  subst L
  rfl

theorem reindex_twice {α : Type*} (m s j N : ℕ) [NeZero j] [NeZero N]
    (h : m * (s * N) = 2 * (j * N)) (q : ZMod N → α) :
    reindex h (iterate m (s * N) (iterate s N q)) = iterate 2 (j * N) (iterate j N q) := by
  funext i
  rw [← ZMod.natCast_zmod_val i, reindex_natCast, iterate_natCast, iterate_natCast,
    iterate_natCast, iterate_natCast]

def fixedIndex {n : ℕ} (F : ReversibleMetric n) (K : ℕ) [NeZero K]
    (q : ZMod K → Sphere n) (t : ℕ) : ℕ :=
  sigNeg ((sndQuad (pen F K 1) (amb q)).restrict (fixed (rotA (n := n) K (t : ZMod K)).toLinearMap))

theorem fixedIndex_reindex {n K L : ℕ} [NeZero K] [NeZero L] (F : ReversibleMetric n)
    (h : K = L) (q : ZMod K → Sphere n) (t : ℕ) :
    fixedIndex F L (reindex h q) t = fixedIndex F K q t := by
  subst L
  rfl

theorem exists_even_half_index {n : ℕ} {F : ReversibleMetric n}
    (g : Finsler.Geodesics.ClosedGeodesic F) (m s j : ℕ) [NeZero m] [NeZero s] [NeZero j]
    (hms : m * s = 2 * j) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N], ∀ a : ℝ,
      sigNeg ((sndQuad (pen F (m * (s * (2 * N))) 1)
        (amb (iterate m (s * (2 * N)) (rootFamily g s N a)))).restrict
          (fixed (rotA (n := n) (m * (s * (2 * N))) (halfIndex m s N)).toLinearMap)) =
        (iterData g).I j := by
  obtain ⟨N₀, hN₀⟩ := SampledHalfIndex.exists_half_index g j
  refine ⟨N₀, fun N hN _ a => ?_⟩
  have hK : m * (s * (2 * N)) = 2 * (j * (2 * N)) := by
    calc
      _ = (m * s) * (2 * N) := by ring
      _ = (2 * j) * (2 * N) := by rw [hms]
      _ = _ := by ring
  have hp := reindex_twice m s j (2 * N) hK
    (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))
  have he := fixedIndex_reindex F hK
    (iterate m (s * (2 * N)) (rootFamily g s N a)) (m * s * N)
  change fixedIndex F (2 * (j * (2 * N)))
    (reindex hK (iterate m (s * (2 * N)) (iterate s (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))))) (m * s * N) = _ at he
  rw [hp] at he
  have hc := hN₀ N hN a
  change fixedIndex F (2 * (j * (2 * N)))
    (iterate 2 (j * (2 * N)) (rootFamily g j N a)) (j * (2 * N)) = (iterData g).I j at hc
  exact he.symm.trans (by rw [show m * s * N = j * (2 * N) by rw [hms]; ring]; exact hc)

end

end Finsler.CircleFixedIndex
