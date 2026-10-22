module

public import Finsler.Geometry.LabelAmbient
public import Finsler.Analysis.FibreQuadratic
public import Finsler.Analysis.LevelGlue

/-! The constants of a label. Let smooth frames G₁, G₂ of the normal space be negative and
positive frames of the normal form on an open set 𝒪 of root polygons inside the smooth set, and
let Γ ⊆ 𝒪 be compact (the root circle). Then the frame coordinates are invertible on 𝒪 (a
negative and a positive frame together form a basis), and there are δ > 0 with the closed
δ-thickening K₀ of Γ inside 𝒪, and R, κ, c > 0, C₁ ≥ 0 such that over K₀ and for coefficients
of norm at most R the penalized energy is C³ at the frame coordinates, the split descent
estimate holds with constants κ and c, and Ψ grows at most quadratically along the fibres with
constant C₁ (its fibre derivative vanishes on the zero section). -/

@[expose] public section

namespace Finsler.LabelData

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.FibreQuadratic Finsler.LevelGlue Finsler.LogCutoff
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)

/-- The fibre derivative of Ψ vanishes on the zero section over the smooth set. -/
theorem fderiv_psi_fibre_zero (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {z : ZMod N → Ambient n} (hz : z ∈ smoothSet m N F) (w : (Fin b → ℝ) × (Fin p → ℝ)) :
    fderiv ℝ (psi m N F G₁ G₂) (z, 0) (0, w) = 0 := by
  have hcoord := coord_contDiff m N G₁ G₂ hG₁ hG₂
  have hz' : ContDiffAt ℝ 3 (pen F (m * N) 1) (iterA m N z) := hz
  have hbase : (z, (0 : (Fin b → ℝ) × (Fin p → ℝ))) + ContinuousLinearMap.inr ℝ
      (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ)) 0 = (z, 0) := by
    rw [map_zero, add_zero]
  have hfib0 : iterA m N z + fibreL m N G₁ G₂ z 0 = iterA m N z := by
    rw [map_zero, add_zero]
  have hpsiAt : ContDiffAt ℝ 3 (psi m N F G₁ G₂) (z, 0) := by
    have h0 : ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, 0)) := by
      rw [coord_zero]
      exact hz'
    exact ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) (z, 0) h0
      (hcoord.contDiffAt.of_le (by simp))
  have hd : DifferentiableAt ℝ (psi m N F G₁ G₂)
      ((z, 0) + ContinuousLinearMap.inr ℝ (ZMod N → Ambient n)
        ((Fin b → ℝ) × (Fin p → ℝ)) 0) := by
    rw [hbase]
    exact hpsiAt.differentiableAt (by norm_num)
  have h1 := fderiv_comp_affine (z, (0 : (Fin b → ℝ) × (Fin p → ℝ)))
    (ContinuousLinearMap.inr ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ))) hd w
  rw [hbase, psi_fibre] at h1
  have hd2 : DifferentiableAt ℝ (pen F (m * N) 1) (iterA m N z + fibreL m N G₁ G₂ z 0) := by
    rw [hfib0]
    exact hz'.differentiableAt (by norm_num)
  have h2 := fderiv_comp_affine (iterA m N z) (fibreL m N G₁ G₂ z) hd2 w
  rw [hfib0] at h2
  change fderiv ℝ (psi m N F G₁ G₂) (z, 0)
    (ContinuousLinearMap.inr ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ)) w) = 0
  rw [← h1, h2]
  exact fderiv_pen_normal m N F 1 (hz'.differentiableAt (by norm_num)) (fibreL_mem m N G₁ G₂ z w)

/-- **The constants of a label.** -/
theorem exists_label_constants (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {𝒪 : Set (ZMod N → Ambient n)} (h𝒪 : IsOpen 𝒪) (h𝒪s : 𝒪 ⊆ smoothSet m N F)
    (hneg : ∀ z ∈ 𝒪, Neg (normalForm m N F z) (G₁ z) ∧ Neg (-normalForm m N F z) (G₂ z))
    {Γ : Set (ZMod N → Ambient n)} (hΓ : IsCompact Γ) (hΓ𝒪 : Γ ⊆ 𝒪) :
    ∃ δ R κ c C₁ : ℝ, 0 < δ ∧ 0 < R ∧ 0 < κ ∧ 0 < c ∧ 0 ≤ C₁ ∧ cthickening δ Γ ⊆ 𝒪 ∧
      (∀ z ∈ cthickening δ Γ, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
        ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
        ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
          fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
            fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2) ∧
      (∀ z ∈ cthickening δ Γ, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
        |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| ≤ C₁ * ‖ξ‖ ^ 2) := by
  obtain ⟨δ, hδ, hsub⟩ := hΓ.exists_cthickening_subset_open h𝒪 hΓ𝒪
  have hK₀ : IsCompact (cthickening δ Γ) := hΓ.cthickening
  have hK₀s : cthickening δ Γ ⊆ smoothSet m N F := hsub.trans h𝒪s
  obtain ⟨R₁, κ, c, hR₁, hκ, hc, hest⟩ := exists_split_descent_coord m N F G₁ G₂ hG₁ hG₂ hK₀
    hK₀s (fun z hz => (hneg z (hsub hz)).1) (fun z hz => (hneg z (hsub hz)).2)
  -- quadratic growth along the fibres
  have hcoord := coord_contDiff m N G₁ G₂ hG₁ hG₂
  have hopen : IsOpen {y : ZMod (m * N) → Ambient n | ContDiffAt ℝ 3 (pen F (m * N) 1) y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact ContDiffAt.eventually hy (by simp)
  set 𝒪' : Set ((ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :=
    coord m N G₁ G₂ ⁻¹' {y | ContDiffAt ℝ 3 (pen F (m * N) 1) y} with h𝒪'def
  have h𝒪' : IsOpen 𝒪' := hopen.preimage hcoord.continuous
  have hΨ : ContDiffOn ℝ 2 (psi m N F G₁ G₂) 𝒪' := fun q hq => by
    have hq' : ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ q) := hq
    have h3 : ContDiffAt ℝ 3 (psi m N F G₁ G₂) q :=
      ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) q hq'
        (hcoord.contDiffAt.of_le (by simp))
    exact (h3.of_le (by norm_num)).contDiffWithinAt
  have hsub0 : ∀ z ∈ cthickening δ Γ, (z, (0 : (Fin b → ℝ) × (Fin p → ℝ))) ∈ 𝒪' := by
    intro z hz
    change ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, 0))
    rw [coord_zero]
    exact hK₀s hz
  obtain ⟨R₂, C₁, hR₂, hC₁, hq⟩ := exists_fibre_quadratic h𝒪' hΨ hK₀ hsub0
    (fun z hz w => fderiv_psi_fibre_zero m N F G₁ G₂ hG₁ hG₂ (hK₀s hz) w)
  refine ⟨δ, min R₁ R₂, κ, c, C₁, hδ, lt_min hR₁ hR₂, hκ, hc, hC₁, hsub, ?_, ?_⟩
  · intro z hz ξ hξ
    exact hest z hz ξ (hξ.trans (min_le_left _ _))
  · intro z hz ξ hξ
    exact (hq z hz ξ (hξ.trans (min_le_right _ _))).2

/-- The frame coordinates are invertible where the frames are a negative and a positive frame
of the normal form. -/
theorem isUnit_of_neg (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    {z : ZMod N → Ambient n}
    (hz : Neg (normalForm m N F z) (G₁ z) ∧ Neg (-normalForm m N F z) (G₂ z)) :
    IsUnit (matA m N G₁ G₂ ψ z) :=
  isUnit_matA m N G₁ G₂ ψ hz.1 hz.2

section Choice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The cutoffs and the small constants of a label.** Around a compact set Γ with a closed
δ-thickening there is a smooth cutoff χ₀ with values in [0, 1], equal to 1 on an open set
containing the closed δ/2-thickening, with compact closed support in the open δ-thickening and
bounded derivative B; for the logarithmic cutoff with M bounding the derivative of the smooth
transition there are λ, r > 0 with r² e^λ ≤ (R/2)² and κ' > 0 with
(C₁ + 1)(B κ' + 2M/λ) ≤ c* / 2, c* = min(c / (b + p + 1), 2). -/
theorem exists_label_choice {Γ : Set E} (hΓ : IsCompact Γ) {δ R c C₁ : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hc : 0 < c) (hC₁ : 0 ≤ C₁) (b p : ℕ) :
    ∃ (χ₀ : E → ℝ) (W₀ : Set E) (B M lam r κ' : ℝ),
      ContDiff ℝ ∞ χ₀ ∧ (∀ z, 0 ≤ χ₀ z ∧ χ₀ z ≤ 1) ∧ HasCompactSupport χ₀ ∧
      tsupport χ₀ ⊆ thickening δ Γ ∧ IsOpen W₀ ∧ cthickening (δ / 2) Γ ⊆ W₀ ∧
      (∀ z ∈ W₀, χ₀ z = 1) ∧ 0 ≤ B ∧ (∀ z, ‖fderiv ℝ χ₀ z‖ ≤ B) ∧
      (∀ x, |deriv Real.smoothTransition x| ≤ M) ∧ 0 < lam ∧ 0 < r ∧
      r ^ 2 * Real.exp lam ≤ (R / 2) ^ 2 ∧ 0 < κ' ∧
      (C₁ + 1) * (B * κ' + 2 * M / lam) ≤ min (c / (b + p + 1)) 2 / 2 := by
  -- the cutoff
  have hT : IsCompact (cthickening (δ / 2) Γ) := hΓ.cthickening
  have hTU : cthickening (δ / 2) Γ ⊆ thickening δ Γ :=
    cthickening_subset_thickening' hδ (half_lt_self hδ) Γ
  obtain ⟨χ₀, W₀, hχ, hχ01, hχc, hχs, hW₀, hTW, hχ1⟩ :=
    exists_cutoff hT isOpen_thickening hTU
  -- the bound of the derivative
  have hdc : HasCompactSupport (fderiv ℝ χ₀) := hχc.fderiv (𝕜 := ℝ)
  have hdcont : Continuous (fderiv ℝ χ₀) := hχ.continuous_fderiv (by simp)
  obtain ⟨B₀, hB₀⟩ := hdc.exists_bound_of_continuous hdcont
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ z, ‖fderiv ℝ χ₀ z‖ ≤ B := fun z => (hB₀ z).trans (le_max_left _ _)
  obtain ⟨M, hM0, hM⟩ := exists_deriv_bound
  -- the constant c*
  set cs : ℝ := min (c / (b + p + 1)) 2 with hcs
  have hcs0 : 0 < cs := lt_min (by positivity) two_pos
  -- λ with (C₁ + 1) 2M/λ ≤ c*/4
  set lam : ℝ := (C₁ + 1) * (8 * M + 1) / cs with hlamdef
  have hlam : 0 < lam := by positivity
  have hlam' : (C₁ + 1) * (2 * M / lam) ≤ cs / 4 := by
    have hC : 0 < C₁ + 1 := by linarith
    rw [hlamdef]
    have e : (C₁ + 1) * (2 * M / ((C₁ + 1) * (8 * M + 1) / cs)) = 2 * M * cs / (8 * M + 1) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  -- r with r² e^λ = (R/2)² e^0 ... we take r = (R/2) e^{-λ/2}
  set r : ℝ := R / 2 * Real.exp (-(lam / 2)) with hrdef
  have hr : 0 < r := by positivity
  have hrR : r ^ 2 * Real.exp lam ≤ (R / 2) ^ 2 := by
    have e : r ^ 2 * Real.exp lam = (R / 2) ^ 2 := by
      rw [hrdef, mul_pow, ← Real.exp_nat_mul]
      rw [mul_assoc, ← Real.exp_add]
      norm_num
      rw [show -(2 * (lam / 2)) + lam = 0 by ring, Real.exp_zero, mul_one]
    rw [e]
  -- κ' with (C₁ + 1) B κ' ≤ c*/4
  set κ' : ℝ := cs / (4 * (C₁ + 1) * (B + 1)) with hκdef
  have hκ' : 0 < κ' := by positivity
  have hκB : (C₁ + 1) * (B * κ') ≤ cs / 4 := by
    have hC : 0 < C₁ + 1 := by linarith
    rw [hκdef]
    have e : (C₁ + 1) * (B * (cs / (4 * (C₁ + 1) * (B + 1)))) = cs / 4 * (B / (B + 1)) := by
      field_simp
    rw [e]
    have h1 : B / (B + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have h2 : 0 ≤ cs / 4 := by positivity
    nlinarith
  refine ⟨χ₀, W₀, B, M, lam, r, κ', hχ, hχ01, hχc, hχs, hW₀, hTW, hχ1, hB0, hB, hM, hlam, hr, hrR,
    hκ', ?_⟩
  have e : (C₁ + 1) * (B * κ' + 2 * M / lam) = (C₁ + 1) * (B * κ') + (C₁ + 1) * (2 * M / lam) := by
    ring
  rw [e]
  linarith

end Choice

end

end Finsler.LabelData
