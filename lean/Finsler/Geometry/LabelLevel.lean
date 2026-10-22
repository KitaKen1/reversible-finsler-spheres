module

public import Finsler.Geometry.LabelRegions
public import Finsler.Geometry.LabelData

/-! The data of a label for the assembly of its level. With the constants of a label on K₀ (the
split estimate and the fibre growth), its cutoffs (v0.120), a root field V₀ bounded by κ' which
does not increase the root functional on K₀ and decreases it strictly at every non-critical
point of K₀, the region U = R(interior K₀, R), the ambient split field W, the deformation β and
the tube T = coord(closure Z₁ × closedBall R₁) satisfy the hypotheses of the assembly of a
level: W is smooth on U, the penalized energy does not increase along W on U and decreases
strictly outside the critical set C (zero coefficients over critical root polygons), the deformed
energy pen + β does the same on the closed support of β, which lies in T ⊆ U. -/

@[expose] public section

namespace Finsler.LabelLevel

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform Finsler.LabelTransport
open Finsler.LabelRegions Finsler.LabelRegion Finsler.LogCutoff
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  {G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m}
  {G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m}
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)

/-- The critical set of a label: zero coefficients over critical root polygons of K₀. -/
def critSet (K₀ : Set (ZMod N → Ambient n)) : Set (ZMod (m * N) → Ambient n) :=
  {Q | IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)) ∧ zOf m N Q ∈ K₀ ∧
    fderiv ℝ (pen F N (1 / m)) (zOf m N Q) = 0 ∧ xiOf m N G₁ G₂ ψ Q = 0}

variable {m N F ψ V₀}

/-- **The data of a label for the assembly of its level.** -/
theorem label_level (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K₀ : Set (ZMod N → Ambient n)} (hK₀c : IsCompact K₀) {R κ c C₁ : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hC₁ : 0 ≤ C₁)
    (hK₀u : ∀ z ∈ K₀, IsUnit (matA m N G₁ G₂ ψ z))
    (hest : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2)
    (hquad : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| ≤ C₁ * ‖ξ‖ ^ 2)
    {χ₀ : (ZMod N → Ambient n) → ℝ} (hχ : ContDiff ℝ ∞ χ₀) (hχ01 : ∀ z, 0 ≤ χ₀ z ∧ χ₀ z ≤ 1)
    {B M lam r κ' : ℝ} (hB : ∀ z, ‖fderiv ℝ χ₀ z‖ ≤ B)
    (hM : ∀ x, |deriv Real.smoothTransition x| ≤ M) (hlam : 0 < lam) (hr : 0 < r)
    (hsmall : (C₁ + 1) * (B * κ' + 2 * M / lam) ≤ min (c / (b + p + 1)) 2 / 2)
    (hκ' : κ' ≤ κ)
    {Z₁ : Set (ZMod N → Ambient n)} (hZ₁ : Bornology.IsBounded Z₁) (hZ₁K : closure Z₁ ⊆ interior K₀)
    (hχZ : tsupport χ₀ ⊆ closure Z₁) {R₁ : ℝ} (hR₁0 : 0 ≤ R₁) (hR₁ : R₁ < R)
    (hrR : r ^ 2 * Real.exp lam ≤ R₁ ^ 2)
    (hnz : ∀ z ∈ closure Z₁, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R₁ →
      ∀ j, coord m N G₁ G₂ (z, ξ) j ≠ 0)
    (hV₀ : ContDiff ℝ ∞ V₀) (hV₀b : ∀ z, ‖V₀ z‖ ≤ κ')
    (hV₀le : ∀ z ∈ K₀, fderiv ℝ (pen F N (1 / m)) z (V₀ z) ≤ 0)
    (hV₀lt : ∀ z ∈ K₀, fderiv ℝ (pen F N (1 / m)) z ≠ 0 →
      fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0) :
    IsOpen (region m N G₁ G₂ ψ (interior K₀) R) ∧
    ContDiffOn ℝ ∞ (splitW m N G₁ G₂ ψ V₀) (region m N G₁ G₂ ψ (interior K₀) R) ∧
    (∀ y ∈ region m N G₁ G₂ ψ (interior K₀) R,
      fderiv ℝ (pen F (m * N) 1) y (splitW m N G₁ G₂ ψ V₀ y) ≤ 0) ∧
    (∀ y ∈ region m N G₁ G₂ ψ (interior K₀) R, y ∉ critSet m N F ψ K₀ (G₁ := G₁) (G₂ := G₂) →
      fderiv ℝ (pen F (m * N) 1) y (splitW m N G₁ G₂ ψ V₀ y) < 0) ∧
    IsCompact (tube m N G₁ G₂ Z₁ R₁) ∧
    tube m N G₁ G₂ Z₁ R₁ ⊆ region m N G₁ G₂ ψ (interior K₀) R ∧
    tsupport (beta m N F G₁ G₂ ψ χ₀ r lam) ⊆ tube m N G₁ G₂ Z₁ R₁ ∧
    (∀ y ∈ tsupport (beta m N F G₁ G₂ ψ χ₀ r lam),
      fderiv ℝ (fun y => pen F (m * N) 1 y + beta m N F G₁ G₂ ψ χ₀ r lam y) y
        (splitW m N G₁ G₂ ψ V₀ y) ≤ 0) ∧
    (∀ y ∈ tsupport (beta m N F G₁ G₂ ψ χ₀ r lam), y ∉ critSet m N F ψ K₀ (G₁ := G₁) (G₂ := G₂) →
      fderiv ℝ (fun y => pen F (m * N) 1 y + beta m N F G₁ G₂ ψ χ₀ r lam y) y
        (splitW m N G₁ G₂ ψ V₀ y) < 0) := by
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    positivity
  have hV₀κ : ∀ z, ‖V₀ z‖ ≤ κ := fun z => (hV₀b z).trans hκ'
  have hint : interior K₀ ⊆ K₀ := interior_subset
  have hest' : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ' →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2 := fun z hz ξ hξ =>
    ⟨(hest z hz ξ hξ).1, fun v hv => (hest z hz ξ hξ).2 v (hv.trans hκ')⟩
  -- the descent estimate of the split field on the region
  have hsplit : ∀ y ∈ region m N G₁ G₂ ψ (interior K₀) R,
      fderiv ℝ (pen F (m * N) 1) y (splitW m N G₁ G₂ ψ V₀ y) ≤
        (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) (zOf m N y) (V₀ (zOf m N y)) -
          c * ‖xiOf m N G₁ G₂ ψ y‖ ^ 2 := by
    rintro y ⟨hu, hz, hx, -⟩
    exact (splitW_le m N F G₁ G₂ ψ V₀ hG₁ hG₂ hest hR.le hV₀κ hV₀le hu (hint hz) hx.le).1
  -- strictness off the critical set
  have hstrict : ∀ y, IsUnit (matA m N G₁ G₂ ψ (zOf m N y)) → zOf m N y ∈ K₀ →
      y ∉ critSet m N F ψ K₀ (G₁ := G₁) (G₂ := G₂) → ∀ e : ℝ, 0 < e →
      (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) (zOf m N y) (V₀ (zOf m N y)) -
        e * ‖xiOf m N G₁ G₂ ψ y‖ ^ 2 < 0 := by
    intro y hu hz hy e he
    have h1 := hV₀le _ hz
    by_cases hxi : xiOf m N G₁ G₂ ψ y = 0
    · have hne : fderiv ℝ (pen F N (1 / m)) (zOf m N y) ≠ 0 := fun h0 => hy ⟨hu, hz, h0, hxi⟩
      have h2 := hV₀lt _ hz hne
      rw [hxi, norm_zero]
      nlinarith
    · have h3 : 0 < ‖xiOf m N G₁ G₂ ψ y‖ := norm_pos_iff.mpr hxi
      have h4 : 0 < e * ‖xiOf m N G₁ G₂ ψ y‖ ^ 2 := by positivity
      nlinarith
  -- the region of the tube
  have htubeU : tube m N G₁ G₂ Z₁ R₁ ⊆ region m N G₁ G₂ ψ (interior K₀) R :=
    tube_subset_region m N ψ hZ₁K hR₁ (fun z hz => hK₀u z (hint (hZ₁K hz))) hnz
  -- the support of the deformation
  have hβsupp : tsupport (beta m N F G₁ G₂ ψ χ₀ r lam) ⊆ tube m N G₁ G₂ Z₁ R₁ := by
    have hsub : tsupport χ₀ ⊆ K₀ ∩ {z | IsUnit (matA m N G₁ G₂ ψ z)} := fun z hz =>
      ⟨hint (hZ₁K (hχZ hz)), hK₀u z (hint (hZ₁K (hχZ hz)))⟩
    obtain ⟨-, hts⟩ := tsupport_beta_subset m N F G₁ G₂ ψ hG₁ hG₂ hK₀c hsub hr.ne' hlam
    refine hts.trans ?_
    rintro _ ⟨⟨z, ξ⟩, ⟨hz, hξ⟩, rfl⟩
    refine ⟨(z, ξ), ⟨hχZ hz, mem_closedBall_zero_iff.mpr ?_⟩, rfl⟩
    have h1 : ‖ξ‖ ^ 2 ≤ R₁ ^ 2 := (sq_norm_le_sqE ξ).trans (hξ.trans hrR)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR₁0 two_ne_zero).mp h1
  -- differentiability of the deformed energy on the region
  have hdiff : ∀ y ∈ region m N G₁ G₂ ψ (interior K₀) R,
      DifferentiableAt ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam) y := by
    rintro y ⟨hu, hz, hx, -⟩
    have hpen : DifferentiableAt ℝ (pen F (m * N) 1) y := by
      have h := (hest _ (hint hz) _ hx.le).1
      rw [coord_inverse m N G₁ G₂ ψ hu] at h
      exact h.differentiableAt (by norm_num)
    have hR0 : 0 ≤ R := hR.le
    have hrR' : r ^ 2 * Real.exp lam ≤ R ^ 2 := hrR.trans (pow_le_pow_left₀ hR₁0 hR₁.le 2)
    have hsuppχ : tsupport χ₀ ⊆ K₀ ∩ {z | IsUnit (matA m N G₁ G₂ ψ z)} := fun z hz =>
      ⟨hint (hZ₁K (hχZ hz)), hK₀u z (hint (hZ₁K (hχZ hz)))⟩
    have hβd := beta_differentiableAt m N F G₁ G₂ ψ hG₁ hG₂ hR0
      (fun z hz ξ hξ => (hest z hz ξ hξ).1) hχ hsuppχ hr.ne' hlam hrR' y
    exact hpen.add hβd
  refine ⟨region_isOpen m N ψ hG₁ hG₂ isOpen_interior R, fun y hy => ?_, fun y hy => ?_,
    fun y hy hyC => ?_, tube_isCompact m N hG₁ hG₂ hZ₁ R₁, htubeU, hβsupp, fun y hy => ?_,
    fun y hy hyC => ?_⟩
  · exact (splitW_contDiffAt m N G₁ G₂ ψ V₀ hG₁ hG₂ hV₀ hy.1).contDiffWithinAt
  · have h := hsplit y hy
    have h1 := hV₀le _ (hint hy.2.1)
    have h2 := sq_nonneg ‖xiOf m N G₁ G₂ ψ y‖
    nlinarith
  · have h := hsplit y hy
    exact lt_of_le_of_lt h (hstrict y hy.1 (hint hy.2.1) hyC c hc)
  · obtain ⟨hu, hz, hx, -⟩ := htubeU (hβsupp hy)
    have h := gDef_splitW_le m N F G₁ G₂ ψ hG₁ hG₂ V₀ hest' hquad hc hC₁ hχ
      (fun z => (hχ01 z).1) (fun z => (hχ01 z).2) hB hr.ne' hlam hM hsmall hu (hint hz) hx.le
      (hV₀b _) (hdiff y (htubeU (hβsupp hy)))
    have hcs : 0 ≤ min (c / (b + p + 1)) 2 / 2 * sqE (xiOf m N G₁ G₂ ψ y) :=
      mul_nonneg (by positivity) (sqE_nonneg _)
    have h1 := hV₀le _ (hint hz)
    change fderiv ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam) y (splitW m N G₁ G₂ ψ V₀ y) ≤ 0
    nlinarith
  · obtain ⟨hu, hz, hx, -⟩ := htubeU (hβsupp hy)
    have h := gDef_splitW_le m N F G₁ G₂ ψ hG₁ hG₂ V₀ hest' hquad hc hC₁ hχ
      (fun z => (hχ01 z).1) (fun z => (hχ01 z).2) hB hr.ne' hlam hM hsmall hu (hint hz) hx.le
      (hV₀b _) (hdiff y (htubeU (hβsupp hy)))
    change fderiv ℝ (gDef m N F G₁ G₂ ψ χ₀ r lam) y (splitW m N G₁ G₂ ψ V₀ y) < 0
    have hcs : 0 < min (c / (b + p + 1)) 2 / 2 := by positivity
    have hsq : sqE (xiOf m N G₁ G₂ ψ y) = ‖eucX (xiOf m N G₁ G₂ ψ y)‖ ^ 2 +
        ‖eucY (xiOf m N G₁ G₂ ψ y)‖ ^ 2 := rfl
    by_cases hxi : xiOf m N G₁ G₂ ψ y = 0
    · have hne : fderiv ℝ (pen F N (1 / m)) (zOf m N y) ≠ 0 := fun h0 => hyC ⟨hu, hint hz, h0, hxi⟩
      have h2 := hV₀lt _ (hint hz) hne
      have hq0 := sqE_nonneg (xiOf m N G₁ G₂ ψ y)
      nlinarith
    · have hpos : 0 < sqE (xiOf m N G₁ G₂ ψ y) := by
        have := sq_norm_le_sqE (xiOf m N G₁ G₂ ψ y)
        have h3 : 0 < ‖xiOf m N G₁ G₂ ψ y‖ := norm_pos_iff.mpr hxi
        nlinarith
      have h1 := hV₀le _ (hint hz)
      nlinarith

end

end Finsler.LabelLevel
