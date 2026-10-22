module

public import Finsler.Geometry.AmbientNormalIndex

/-! Fixed signed-coordinate, energy, flow and index comparison. -/

@[expose] public section

namespace Finsler.FixedIterateIndex

open Module QuadraticMap QuadraticForm
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty
open Finsler.AmbientHessian Finsler.AmbientSymmetry Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 5

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

theorem sigNeg_fixed_pen_iterate (F : ReversibleMetric n) (lam : ℝ)
    (q₀ : ZMod N → Sphere n)
    (hf : ContDiffAt ℝ 2 (pen F (m * N) lam) (amb (iterate m N q₀))) :
    sigNeg ((sndQuad (pen F (m * N) lam) (amb (iterate m N q₀))).restrict
      (fixed (rotL (n := n) m N))) = sigNeg (sndQuad (pen F N (lam / m)) (amb q₀)) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hp : amb (iterate m N q₀) = iterate m N (amb q₀) := rfl
  have hequiv : QuadraticMap.Equivalent ((m : ℝ) ^ 2 • sndQuad (pen F N (lam / m)) (amb q₀))
      ((sndQuad (pen F (m * N) lam) (amb (iterate m N q₀))).restrict
        (fixed (rotL (n := n) m N))) :=
    ⟨⟨(LinearEquiv.ofInjective (iterA (n := n) m N).toLinearMap (iterA_injective m N)).trans
        (LinearEquiv.ofEq _ _ (fixed_rotL m N).symm), fun v => by
      change sndQuad (pen F (m * N) lam) (amb (iterate m N q₀)) (iterA m N v) =
        (m : ℝ) ^ 2 • sndQuad (pen F N (lam / m)) (amb q₀) v
      rw [sndQuad_apply, sndQuad_apply, smul_eq_mul, hp]
      exact sndDeriv_iterate m N F lam (by rw [← hp]; exact hf) v v⟩⟩
  rw [← hequiv.sigNeg_eq, QuadraticForm.sigNeg_smul_of_pos _ hm2]

theorem sigNeg_fixed_pen_index (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    (q₀ : ZMod N → Sphere n) (hq₀ : ShortPolygon δ q₀)
    (hne₀ : ∀ i, q₀ (i + 1) ≠ q₀ i) (hc₀ : PolyCritical F N q₀)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : ContDiffAt ℝ 2 (pen F (m * N) lam) (amb (iterate m N q₀)))
    (hs₀ : (hessian F q₀).toLinearMap.IsSymmetric) :
    sigNeg ((sndQuad (pen F (m * N) lam) (amb (iterate m N q₀))).restrict
      (fixed (rotL (n := n) m N))) = index F q₀ hs₀ := by
  rw [sigNeg_fixed_pen_iterate m N F lam q₀ hf]
  exact sigNeg_sndQuad_pen F hδ hq₀ hne₀ hc₀ (div_nonneg hlam (Nat.cast_nonneg m)) hs₀

end

end Finsler.FixedIterateIndex
