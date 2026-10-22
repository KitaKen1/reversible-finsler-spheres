module

public import Finsler.Geometry.AmbientSplitField

/-! The root field and the descent region near a critical circle. The penalized energy of the
root polygons with weight 1/m is m^{-2} times the penalized energy (weight 1) at their m-fold
iterates, so it is C³ wherever the latter is C³ at the iterate. If the root functional has no
critical point in a compact set K₀ of root polygons at distance at least r from a set Γ (the
circle of the root polygons), there is a smooth compactly supported pseudo-gradient V₀ of the
root functional with values bounded by any prescribed κ > 0, along which the root functional
does not increase on the smooth set and decreases strictly on that part of K₀. With the
constants of the split descent estimate, the ambient split field built from V₀ is a descent
field of the penalized energy on the coordinate region over K₀, strictly where the coefficients
do not vanish or the root polygon is at distance at least r from Γ. -/

@[expose] public section

namespace Finsler.LabelRegion

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n)

/-- The root functional is C³ at the root polygons whose iterates lie in the smooth set. -/
theorem pen_root_contDiffAt {z : ZMod N → Ambient n} (hz : z ∈ smoothSet m N F) :
    ContDiffAt ℝ 3 (pen F N (1 / m)) z := by
  have hz' : ContDiffAt ℝ 3 (pen F (m * N) 1) (iterA m N z) := hz
  have h1 : ContDiffAt ℝ 3 (fun y => ((m : ℝ) ^ 2)⁻¹ * pen F (m * N) 1 (iterA m N y)) z :=
    contDiffAt_const.mul (ContDiffAt.comp (g := pen F (m * N) 1) (f := iterA (n := n) m N) z hz'
      (iterA (n := n) m N).contDiff.contDiffAt)
  have hm : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne m))
  have e : (fun y => ((m : ℝ) ^ 2)⁻¹ * pen F (m * N) 1 (iterA m N y)) = pen F N (1 / m) := by
    funext y
    rw [show iterA m N y = iterate m N y from rfl, pen_iterate, ← mul_assoc, inv_mul_cancel₀ hm,
      one_mul]
  rw [e] at h1
  exact h1

/-- **The root field.** If the root functional has no critical point in the part of a compact
set K₀ ⊆ smoothSet at distance at least r from Γ, there is a smooth compactly supported field V₀
supported in the smooth set, bounded by κ, along which the root functional does not increase on
the smooth set and decreases strictly on that part of K₀. -/
theorem exists_root_field {K₀ Γ : Set (ZMod N → Ambient n)} (hK₀ : IsCompact K₀)
    (hK₀s : K₀ ⊆ smoothSet m N F) {r : ℝ}
    (hiso : ∀ z ∈ K₀, r ≤ infDist z Γ → fderiv ℝ (pen F N (1 / m)) z ≠ 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n, ContDiff ℝ ∞ V₀ ∧ HasCompactSupport V₀ ∧
      tsupport V₀ ⊆ smoothSet m N F ∧
      (∀ z ∈ smoothSet m N F, fderiv ℝ (pen F N (1 / m)) z (V₀ z) ≤ 0) ∧
      (∀ z ∈ K₀, r ≤ infDist z Γ → fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0) ∧
      ∀ z, ‖V₀ z‖ ≤ κ := by
  have hf : ContDiffOn ℝ 1 (pen F N (1 / m)) (smoothSet m N F) := fun z hz =>
    ((pen_root_contDiffAt m N F hz).of_le (by norm_num)).contDiffWithinAt
  have hA : IsCompact (K₀ ∩ {z | r ≤ infDist z Γ}) :=
    hK₀.inter_right (isClosed_le continuous_const (continuous_infDist_pt Γ))
  obtain ⟨V₀, hV, hVc, hVs, hle, hlt, hb⟩ := exists_small_pseudoGradient
    (smoothSet_isOpen m N F) hf hA (fun z hz => hK₀s hz.1) (fun z hz => hiso z hz.1 hz.2) hκ
  exact ⟨V₀, hV, hVc, hVs, hle, fun z hz hr => hlt z ⟨hz, hr⟩, hb⟩

variable {b p : ℕ} (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)

/-- **Descent on the coordinate region.** With the constants of the split descent estimate on
K₀ and a root field V₀ bounded by κ which does not increase the root functional on K₀, the
ambient split field is a descent field of the penalized energy at the ambient polygons whose
root polygon lies in K₀, whose coefficients have norm at most R and at which the frame
coordinates are invertible; the derivative is at most -c ‖ξ‖², and it is negative if moreover
the root polygon is at distance at least r from Γ and V₀ decreases the root functional strictly
there. -/
theorem splitW_le (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K₀ : Set (ZMod N → Ambient n)} {R κ c : ℝ}
    (hest : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2) (hR : 0 ≤ R)
    (hb : ∀ z, ‖V₀ z‖ ≤ κ) (hle : ∀ z ∈ K₀, fderiv ℝ (pen F N (1 / m)) z (V₀ z) ≤ 0)
    {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (hz : zOf m N Q ∈ K₀) (hξ : ‖xiOf m N G₁ G₂ ψ Q‖ ≤ R) :
    fderiv ℝ (pen F (m * N) 1) Q (splitW m N G₁ G₂ ψ V₀ Q) ≤
      (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) (zOf m N Q) (V₀ (zOf m N Q)) -
        c * ‖xiOf m N G₁ G₂ ψ Q‖ ^ 2 ∧
    fderiv ℝ (pen F (m * N) 1) Q (splitW m N G₁ G₂ ψ V₀ Q) ≤
      -(c * ‖xiOf m N G₁ G₂ ψ Q‖ ^ 2) := by
  have h := splitW_descent m N F G₁ G₂ ψ V₀ hG₁ hG₂ hest hQ hz hξ (hb _) hR
  have h1 := hle _ hz
  have h2 : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
  refine ⟨h, ?_⟩
  nlinarith

end

end Finsler.LabelRegion
