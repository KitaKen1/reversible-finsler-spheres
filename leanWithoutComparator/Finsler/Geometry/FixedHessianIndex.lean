module

public import Finsler.Analysis.CommutingFixedIndex
public import Finsler.Geometry.FixedNormalIndex
public import Finsler.Geometry.FixedIterateIndex

/-! The actual ambient polygon Hessian splits into fixed root and fixed normal parts.
Its normal fixed index differs from the full fixed index by at most the ordinary root
index. Signed frame coordinates identify the normal fixed index with the fixed shift. -/

@[expose] public section

namespace Finsler.FixedHessianIndex

open Module QuadraticMap QuadraticForm Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty
open Finsler.AmbientHessian Finsler.AmbientSymmetry Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.CircleFrameField Finsler.NormalFamily
open Finsler.FrameCoordinates Finsler.InvolutionIndex Finsler.DefiniteFrames
open Finsler.FixedIterateIndex Finsler.FixedNormalIndex Finsler.RotationNatural

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

def normalFixedEquiv (s : ZMod (m * N)) :
    Module.End.eigenspace (rotV (n := n) m N s).toLinearMap 1 ≃ₗ[ℝ]
      ↥(normal (rotL (n := n) m N) m ⊓ fixed (rotA (n := n) (m * N) s).toLinearMap) where
  toFun v := ⟨v.1.1, v.1.2, by
    exact (mem_fixed (rotA (n := n) (m * N) s).toLinearMap v.1.1).mpr
      (congrArg Subtype.val ((Module.End.mem_eigenspace_iff.mp v.2).trans (one_smul _ _)))⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    apply Subtype.ext
    exact (mem_fixed _ w.1).mp w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sigNeg_normal_fixed (F : ReversibleMetric n) (z : ZMod N → Ambient n)
    (s : ZMod (m * N)) :
    sigNeg ((sndQuad (pen F (m * N) 1) (iterA m N z)).restrict
      (normal (rotL (n := n) m N) m ⊓ fixed (rotA (n := n) (m * N) s).toLinearMap)) =
      sigNeg (LinearMap.BilinMap.toQuadraticMap
        (eigenForm (rotV m N s).toLinearMap 1 (normalForm m N F z))) := by
  have he : QuadraticMap.Equivalent
      (LinearMap.BilinMap.toQuadraticMap (eigenForm (rotV m N s).toLinearMap 1 (normalForm m N F z)))
      ((sndQuad (pen F (m * N) 1) (iterA m N z)).restrict
        (normal (rotL (n := n) m N) m ⊓ fixed (rotA (n := n) (m * N) s).toLinearMap)) :=
    ⟨⟨normalFixedEquiv m N s, fun _ => rfl⟩⟩
  exact he.sigNeg_eq.symm

theorem sigNeg_fixed_normal_bounds (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    (q₀ : ZMod N → Sphere n) (hq₀ : ShortPolygon δ q₀)
    (hne₀ : ∀ i, q₀ (i + 1) ≠ q₀ i) (hc₀ : PolyCritical F N q₀)
    (hf : ContDiffAt ℝ 2 (pen F (m * N) 1) (amb (iterate m N q₀)))
    (hs₀ : (hessian F q₀).toLinearMap.IsSymmetric) (s : ZMod (m * N)) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
        (eigenForm (rotV m N s).toLinearMap 1 (normalForm m N F (amb q₀)))) ≤
      sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
        (fixed (rotA (n := n) (m * N) s).toLinearMap)) ∧
      sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
        (fixed (rotA (n := n) (m * N) s).toLinearMap)) ≤
        index F q₀ hs₀ + sigNeg (LinearMap.BilinMap.toQuadraticMap
          (eigenForm (rotV m N s).toLinearMap 1 (normalForm m N F (amb q₀)))) := by
  let β := (fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (amb (iterate m N q₀))).toLinearMap₁₂
  have hsym : ∀ v w, β v w = β w v := fun v w =>
    (hf.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq v w
  have hpoint : rotA (m * N) (N : ZMod (m * N)) (amb (iterate m N q₀)) =
      amb (iterate m N q₀) := rotA_iterate m N (amb q₀)
  have hinv : ∀ v w, β (rotL m N v) (rotL m N w) = β v w := fun v w =>
    sndDeriv_invariant (rotA (n := n) (m * N) (N : ZMod (m * N)))
      (fun x => pen_rotA (m * N) F 1 _ x) hpoint hf v w
  have hcomm : ∀ v : ZMod (m * N) → Ambient n,
      rotA (m * N) s (rotL m N v) = rotL m N (rotA (m * N) s v) := by
    intro v
    simpa only [pow_one] using (rotL_pow_rotA m N s 1 v).symm
  have h := Finsler.CommutingFixedIndex.sigNeg_fixed_bounds (rotL (n := n) m N)
    (rotA (n := n) (m * N) s).toLinearMap m hcomm
    (Nat.pos_of_ne_zero (NeZero.ne m)) (rotL_pow m N) β hsym hinv
  change sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
      (normal (rotL m N) m ⊓ fixed (rotA (m * N) s).toLinearMap)) ≤
      sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
        (fixed (rotA (m * N) s).toLinearMap)) ∧
    sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
        (fixed (rotA (m * N) s).toLinearMap)) ≤
      sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict (fixed (rotL m N))) +
        sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
          (normal (rotL m N) m ⊓ fixed (rotA (m * N) s).toLinearMap)) at h
  rw [sigNeg_fixed_pen_index m N F hδ q₀ hq₀ hne₀ hc₀ zero_le_one hf hs₀] at h
  have hnf := sigNeg_normal_fixed m N F (amb q₀) s
  change sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
    (normal (rotL m N) m ⊓ fixed (rotA (m * N) s).toLinearMap)) = _ at hnf
  rw [hnf] at h
  exact h

variable {b p : ℕ}
variable (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
variable (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
variable (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))

include ψ in
theorem fixed_shift_bounds (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    (q₀ : ZMod N → Sphere n) (hq₀ : ShortPolygon δ q₀)
    (hne₀ : ∀ i, q₀ (i + 1) ≠ q₀ i) (hc₀ : PolyCritical F N q₀)
    (hf : ContDiffAt ℝ 2 (pen F (m * N) 1) (amb (iterate m N q₀)))
    (hs₀ : (hessian F q₀).toLinearMap.IsSymmetric)
    (hneg : Neg (normalForm m N F (amb q₀)) (G₁ (amb q₀)))
    (hpos : Neg (-normalForm m N F (amb q₀)) (G₂ (amb q₀)))
    (s : ZMod (m * N)) (hfix : rotA N (red m N s) (amb q₀) = amb q₀)
    (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ i, G₁ (rotA N (red m N s) (amb q₀)) i = d₁ i • rotV m N s (G₁ (amb q₀) i))
    (h₂ : ∀ i, G₂ (rotA N (red m N s) (amb q₀)) i = d₂ i • rotV m N s (G₂ (amb q₀) i)) :
    Fintype.card {i : Fin b // d₁ i = 1} ≤
      sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
        (fixed (rotA (n := n) (m * N) s).toLinearMap)) ∧
      sigNeg ((sndQuad (pen F (m * N) 1) (amb (iterate m N q₀))).restrict
        (fixed (rotA (n := n) (m * N) s).toLinearMap)) ≤
        index F q₀ hs₀ + Fintype.card {i : Fin b // d₁ i = 1} := by
  have h := sigNeg_fixed_normal_bounds m N F hδ q₀ hq₀ hne₀ hc₀ hf hs₀ s
  rw [sigNeg_fixed_normal G₁ G₂ ψ (amb q₀) (normalForm m N F (amb q₀)) hneg hpos
    s hfix d₁ d₂ hd₁ hd₂ h₁ h₂] at h
  exact h

end

end Finsler.FixedHessianIndex
