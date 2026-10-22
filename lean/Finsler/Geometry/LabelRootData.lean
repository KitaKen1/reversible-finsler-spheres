module

public import Finsler.Geometry.LabelPack
public import Finsler.Geometry.RootTubeData
public import Finsler.Geometry.RootFlowFixed
public import Finsler.Geometry.RootField
public import Finsler.Geometry.InvariantLabelChoice
public import Finsler.Geometry.LabelRegionRotation
public import Finsler.Geometry.LabelSetRotation
public import Finsler.Geometry.RootFieldRotation

/-! Retain the actual bounded equivariant root ODE, nested margins and label tube witnesses. -/

@[expose] public section

namespace Finsler.LabelRootData

open Finsler.LabelPack
open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.NormalFamily
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform Finsler.LabelTransport
open Finsler.LabelRegions Finsler.LabelData Finsler.LabelLevel Finsler.LevelField
open Finsler.LabelRegion Finsler.AmbientDescent Finsler.FlowLens Finsler.LogCutoff
open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LensContinuation Finsler.ProductModel
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {m N : ℕ} [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  {G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m}
  {G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m}


set_option maxHeartbeats 1800000 in
theorem exists_root_tube_data (hn : 1 ≤ n) (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (a : ZMod (m * N)) (ha : a + a = 0)
    {𝒪 : Set (ZMod N → Ambient n)} (h𝒪 : IsOpen 𝒪) (h𝒪s : 𝒪 ⊆ smoothSet m N F)
    (hneg : ∀ z ∈ 𝒪, Neg (normalForm m N F z) (G₁ z) ∧ Neg (-normalForm m N F z) (G₂ z))
    (h𝒪nz : ∀ z ∈ 𝒪, ∀ j, z j ≠ 0)
    {Γ : Set (ZMod N → Ambient n)} (hΓ : IsCompact Γ) (hΓ𝒪 : Γ ⊆ 𝒪)
    (hΓτ : ∀ z ∈ Γ, rotA N (red m N a) z ∈ Γ)
    {a₀ b₀ : ℝ}
    (hΓval : ∀ z ∈ Γ, a₀ < (m : ℝ) ^ 2 * pen F N (1 / m) z ∧ (m : ℝ) ^ 2 * pen F N (1 / m) z < b₀)
    (hroot : ∀ κ : ℝ, 0 < κ → ∃ V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n,
      ContDiff ℝ ∞ V₀ ∧ HasCompactSupport V₀ ∧ tsupport V₀ ⊆ regSet F N (1 / m) ∧
      (∀ z, ‖V₀ z‖ ≤ κ) ∧
      (∀ z ∈ regSet F N (1 / m), fderiv ℝ (pen F N (1 / m)) z (V₀ z) ≤ 0) ∧
      ∀ z ∈ regSet F N (1 / m), a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z →
        (m : ℝ) ^ 2 * pen F N (1 / m) z ≤ b₀ → fderiv ℝ (pen F N (1 / m)) z ≠ 0 →
        fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0)
    (hKr : IsCompact {z : Om n N | a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀})
    (hbandreg : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → Q.1 ∈ regSet F N (1 / m))
    {Wrest : Set (Om n N)} (hWrest : IsOpen Wrest) {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hWΓ : ∀ Q ∈ Wrest, Q.1 ∉ thickening δ₁ Γ)
    (hrcrit : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → fderiv ℝ (pen F N (1 / m)) Q.1 = 0 →
        Q.1 ∈ Γ ∨ Q ∈ Wrest)
    {𝒰 : Set (ZMod (m * N) → Ambient n)} (h𝒰 : IsOpen 𝒰) (hΓ𝒰 : ∀ z ∈ Γ, reidx (rfl : m * N = m * N) (iterA m N z) ∈ 𝒰)
    {c₀ : ℝ} (ha₀c₀ : a₀ < c₀) (hc₀b₀ : c₀ < b₀)
    (hΓc₀ : ∀ z ∈ Γ, (m : ℝ) ^ 2 * pen F N (1 / m) z = c₀)
    (hrval : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → fderiv ℝ (pen F N (1 / m)) Q.1 = 0 →
        (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 = c₀)
    {η : ℝ} (hη : 0 < η) :
    Nonempty (RootTubeData F (G₁ := G₁) (G₂ := G₂) ψ a Γ Wrest a₀ b₀ c₀ 𝒰) := by
  classical
  let τ := rotA (n := n) N (red m N a)
  have hred : red m N a + red m N a = 0 := by rw [← map_add, ha, map_zero]
  have hτ : ∀ z, τ (τ z) = z := Finsler.PolygonDescentK.rotA_involutive hred
  have hτiso : Isometry τ := by
    apply Isometry.of_dist_eq
    intro z z'
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact Finsler.RotationNatural.norm_rotA N (red m N a) (z - z')
  have hth : ∀ R z, τ z ∈ thickening R Γ ↔ z ∈ thickening R Γ :=
    Finsler.InvariantThickening.thickening_invariant τ hτ hΓτ hτiso
  have hcth : ∀ R z, τ z ∈ cthickening R Γ ↔ z ∈ cthickening R Γ :=
    Finsler.InvariantThickening.cthickening_invariant τ hτ hΓτ hτiso
  -- 𝒪 lies in the regular set of the root functional
  have h𝒪r : 𝒪 ⊆ regSet F N (1 / m) := fun z hz =>
    ⟨h𝒪nz z hz, (pen_root_contDiffAt m N F (h𝒪s hz)).of_le (by norm_num)⟩
  -- the open band set, kept away from Wrest
  obtain ⟨𝒪', h𝒪'o, hΓ𝒪', h𝒪'𝒪, h𝒪'val, h𝒪'𝒰⟩ :=
    exists_band_thickening F h𝒪 h𝒪r hΓ𝒪 hΓval h𝒰 hΓ𝒰
  have h𝒪₂ : IsOpen (𝒪' ∩ thickening δ₁ Γ) := h𝒪'o.inter isOpen_thickening
  have hΓ𝒪₂ : Γ ⊆ 𝒪' ∩ thickening δ₁ Γ := fun z hz =>
    ⟨hΓ𝒪' hz, self_subset_thickening hδ₁ Γ hz⟩
  have h𝒪₂𝒪 : 𝒪' ∩ thickening δ₁ Γ ⊆ 𝒪 := fun z hz => h𝒪'𝒪 hz.1
  -- the constants on K₀ = cthickening δ Γ
  obtain ⟨δ, R, κ, c, C₁, hδ, hR, hκ, hc, hC₁, hK₀sub, hest, hquad⟩ :=
    exists_label_constants m N F G₁ G₂ hG₁ hG₂ h𝒪₂ (h𝒪₂𝒪.trans h𝒪s)
      (fun z hz => hneg z (h𝒪₂𝒪 hz)) hΓ hΓ𝒪₂
  have hK₀c : IsCompact (cthickening δ Γ) := hΓ.cthickening
  have hK₀𝒪 : ∀ z ∈ cthickening δ Γ, z ∈ 𝒪 := fun z hz => h𝒪₂𝒪 (hK₀sub hz)
  have hK₀u : ∀ z ∈ cthickening δ Γ, IsUnit (matA m N G₁ G₂ ψ z) := fun z hz =>
    isUnit_of_neg m N F G₁ G₂ ψ (hneg z (hK₀𝒪 z hz))
  have hK₀nz : ∀ z ∈ cthickening δ Γ, ∀ j, z j ≠ 0 := fun z hz => h𝒪nz z (hK₀𝒪 z hz)
  have hK₀reg : cthickening δ Γ ⊆ regSet F N (1 / m) := fun z hz => h𝒪r (hK₀𝒪 z hz)
  have hK₀val : ∀ z ∈ cthickening δ Γ, a₀ < (m : ℝ) ^ 2 * pen F N (1 / m) z ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z < b₀ := fun z hz => h𝒪'val z (hK₀sub hz).1
  have hK₀δ₁ : cthickening δ Γ ⊆ thickening δ₁ Γ := fun z hz => (hK₀sub hz).2
  -- tubes: nonzero vertices and the open set 𝒰
  obtain ⟨Rnz, hRnz, hnzK⟩ := exists_nonzero_tube m N hG₁ hG₂ hK₀c hK₀nz
  have hpre : IsOpen (coord m N G₁ G₂ ⁻¹' 𝒰) :=
    h𝒰.preimage (coord_contDiff m N G₁ G₂ hG₁ hG₂).continuous
  obtain ⟨R𝒰, hR𝒰, h𝒰tube⟩ := Finsler.NormalExpansion.exists_tube hpre hK₀c
    (fun z hz => by
      change coord m N G₁ G₂ (z, 0) ∈ 𝒰
      rw [coord_zero]
      exact h𝒪'𝒰 z (hK₀sub hz).1)
  -- the radius R₂
  have hC₁1 : 0 < C₁ + 1 := by linarith only [hC₁]
  set Rη : ℝ := min 1 (η / (C₁ + 1)) with hRηdef
  have hRη : 0 < Rη := lt_min one_pos (by positivity)
  set R₂ : ℝ := min R (min Rnz (min R𝒰 Rη)) with hR₂def
  have hR₂ : 0 < R₂ := lt_min hR (lt_min hRnz (lt_min hR𝒰 hRη))
  have hR₂R : R₂ ≤ R := min_le_left _ _
  have hR₂nz : R₂ ≤ Rnz := (min_le_right _ _).trans (min_le_left _ _)
  have hR₂𝒰 : R₂ ≤ R𝒰 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hR₂η : R₂ ≤ Rη := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the cutoffs and the small constants
  obtain ⟨χ₀, W₀, B, M, lam, r, κ', hχ, hχ01, hχc, hχs, hχτ, hWτ, hW₀, hTW, hχ1, hB0, hB, hM, hlam, hr,
    hrR, hκ'0, hsmall⟩ := Finsler.InvariantLabelChoice.exists_invariant_label_choice
      τ hτ hτiso hΓτ hΓ (half_pos hδ) hR₂ hc hC₁ b p
  -- the sets and radii
  set R₁ : ℝ := R₂ / 2 with hR₁def
  set κ'' : ℝ := min κ' (min κ (δ / 32)) with hκ''def
  set ρ : ℝ := min R₁ (r / 2) with hρdef
  set ρ' : ℝ := ρ / Real.exp 1 with hρ'def
  have hκ'' : 0 < κ'' := lt_min hκ'0 (lt_min hκ (by positivity))
  have hR₁ : 0 < R₁ := half_pos hR₂
  have hρ : 0 < ρ := lt_min hR₁ (half_pos hr)
  have hR₁R₂ : R₁ < R₂ := half_lt_self hR₂
  have hR₁nz : R₁ ≤ Rnz := by rw [hR₁def]; linarith only [hR₂nz, hR₂]
  have hκ''κ' : κ'' ≤ κ' := min_le_left _ _
  have hκ''κ : κ'' ≤ κ := (min_le_right _ _).trans (min_le_left _ _)
  have hκ''δ : κ'' ≤ δ / 32 := (min_le_right _ _).trans (min_le_right _ _)
  have hρR₁ : ρ ≤ R₁ := min_le_left _ _
  have hρr2 : ρ ≤ r / 2 := min_le_right _ _
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith only [this]
  have hρ'ρ : ρ' ≤ ρ := div_le_self hρ.le he1
  have hρ'0 : 0 < ρ' := div_pos hρ (Real.exp_pos 1)
  have hρ'e : ρ' * Real.exp 1 ≤ ρ := le_of_eq (div_mul_cancel₀ ρ (Real.exp_pos 1).ne')
  have hrR₂ : r ^ 2 * Real.exp lam ≤ R₂ ^ 2 :=
    hrR.trans (by rw [hR₁def]; exact pow_le_pow_left₀ (by positivity) (half_le_self hR₂.le) 2)
  clear_value ρ' ρ κ'' R₁
  have hthK : thickening δ Γ ⊆ cthickening δ Γ := thickening_subset_cthickening δ Γ
  have hclZ₁ : closure (thickening (3 * δ / 4) Γ) ⊆ interior (cthickening δ Γ) := by
    have h1 : closure (thickening (3 * δ / 4) Γ) ⊆ cthickening (3 * δ / 4) Γ :=
      closure_thickening_subset_cthickening _ Γ
    have h2 : cthickening (3 * δ / 4) Γ ⊆ thickening δ Γ :=
      cthickening_subset_thickening' hδ (by linarith only [hδ]) Γ
    exact (h1.trans h2).trans (interior_maximal hthK isOpen_thickening)
  have hZ₁K : thickening (3 * δ / 4) Γ ⊆ cthickening δ Γ :=
    (thickening_mono (by linarith only [hδ]) Γ).trans hthK
  have hZ₀Z₁ : thickening (δ / 8) Γ ⊆ thickening (3 * δ / 4) Γ := thickening_mono (by linarith only [hδ]) Γ
  have hZ₀'Z₀ : thickening (δ / 16) Γ ⊆ thickening (δ / 8) Γ := thickening_mono (by linarith only [hδ]) Γ
  have hχZ : tsupport χ₀ ⊆ closure (thickening (3 * δ / 4) Γ) :=
    hχs.trans ((thickening_mono (by linarith only [hδ]) Γ).trans subset_closure)
  have hχ1Z₀ : ∀ z ∈ thickening (δ / 8) Γ, χ₀ z = 1 := fun z hz =>
    hχ1 z (hTW (thickening_subset_cthickening _ Γ (thickening_mono (by linarith only [hδ]) Γ hz)))
  -- the root field
  obtain ⟨Vraw, hraw, hrawc, hrawt, hrawb, hrawle, hrawlt⟩ := hroot κ'' hκ''
  let V₀ := Finsler.EquivariantApprox.average τ τ Vraw
  obtain ⟨hV₀, hV₀c, hV₀t, hV₀b, hV₀le, hV₀τ, hstrict⟩ :=
    Finsler.RootFieldRotation.average_root_field F (1 / m) (red m N a) hred
      hraw hrawc hrawt hrawb hrawle
  have hV₀lt : ∀ z ∈ regSet F N (1 / m), a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z →
      (m : ℝ) ^ 2 * pen F N (1 / m) z ≤ b₀ → fderiv ℝ (pen F N (1 / m)) z ≠ 0 →
      fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0 :=
    fun z hz hza hzb hne => hstrict z (hrawlt z hz hza hzb hne)
  obtain ⟨K₀', hL₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hV₀c hV₀ (by simp)
  have hsupp₀ : ∀ z, V₀ z ≠ 0 → z ∈ regSet F N (1 / m) := fun z hz =>
    hV₀t (subset_tsupport V₀ hz)
  have hV00 : ∀ z, V₀ z ≠ 0 → ∀ j, z j ≠ 0 := fun z hz => (hsupp₀ z hz).1
  have hg₀ : ∀ z ∈ regSet F N (1 / m),
      DifferentiableAt ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z := fun z hz =>
    (hz.2.differentiableAt one_ne_zero).const_mul _
  have hfd : ∀ z ∈ regSet F N (1 / m), ∀ v,
      fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z v =
        (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) z v := by
    intro z hz v
    rw [fderiv_const_mul (hz.2.differentiableAt one_ne_zero), smul_apply, smul_eq_mul]
  have hle₀ : ∀ z ∈ regSet F N (1 / m),
      fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z (V₀ z) ≤ 0 := by
    intro z hz
    rw [hfd z hz]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hV₀le z hz)
  have hh : Continuous fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1 :=
    continuous_const.mul (penW_continuous F hn (1 / m))
  have hnzZ₁ : ∀ z ∈ closure (thickening (3 * δ / 4) Γ), ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ),
      ‖ξ‖ ≤ R₁ → ∀ j, coord m N G₁ G₂ (z, ξ) j ≠ 0 := fun z hz ξ hξ =>
    hnzK z (interior_subset (hclZ₁ hz)) ξ (hξ.trans hR₁nz)
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    exact sq_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos m))
  have hdisr : Disjoint {z : Om n N | z.1 ∈ thickening (δ / 8) Γ} Wrest := by
    rw [Set.disjoint_left]
    intro z hz hzW
    exact hWΓ z hzW (hK₀δ₁ (hZ₁K (hZ₀Z₁ hz)))
  have hstrictr : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ →
      z ∉ {z : Om n N | z.1 ∈ thickening (δ / 16) Γ} ∪ Wrest →
      (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
    intro z h1 h2 hz
    have hne : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := by
      intro h0
      rcases hrcrit z h1 h2 h0 with hΓz | hW
      · exact hz (Or.inl (self_subset_thickening (by positivity) Γ hΓz))
      · exact hz (Or.inr hW)
    have hreg := hbandreg z h1 h2
    have hlt := hV₀lt z.1 hreg h1 h2 hne
    have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
      rw [hfd z.1 hreg]
      exact mul_neg_of_pos_of_neg hm2 hlt
    exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
  have hmargin : ∀ z ∈ thickening (δ / 16) Γ, ∀ z' : ZMod N → Ambient n, ‖z' - z‖ ≤ κ'' →
      z' ∈ thickening (δ / 8) Γ := by
    intro z hz z' hz'
    exact margin_thickening (κ := κ'') (by linarith only [hκ''δ, hδ]) hz
      (by rw [dist_eq_norm]; exact hz')
  have hψstrict : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≠ c₀ →
      (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
    intro z h1 h2 hne
    have hne' : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := fun h0 => hne (hrval z h1 h2 h0)
    have hreg := hbandreg z h1 h2
    have hlt := hV₀lt z.1 hreg h1 h2 hne'
    have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
      rw [hfd z.1 hreg]
      exact mul_neg_of_pos_of_neg hm2 hlt
    exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
  have hregion : IsOpen (region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁) :=
    region_isOpen m N ψ hG₁ hG₂ isOpen_thickening R₁
  have hUsub : region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁ ⊆ 𝒰 := by
    rintro Q ⟨hu, hz, hx, _⟩
    have hxR : ‖xiOf m N G₁ G₂ ψ Q‖ ≤ R𝒰 := hx.le.trans (by
      rw [hR₁def]
      linarith only [hR₂𝒰, hR₂])
    have h := h𝒰tube (zOf m N Q) (hZ₁K hz) (xiOf m N G₁ G₂ ψ Q) hxR
    rw [mem_preimage, coord_inverse m N G₁ G₂ ψ hu] at h
    exact h
  refine ⟨{
    lower := ha₀c₀, upper := hc₀b₀, circle_value := hΓc₀,
    rest_open := hWrest, compact_band := hKr,
    V := V₀, K := K₀', lipschitz := hL₀, nonzero := hV00, diff := hg₀,
    supp := hsupp₀, nonpos := hle₀, κ := κ'', ρ := ρ, κ_pos := hκ'', ρ_pos := hρ,
    bound := hV₀b, Z := thickening (δ / 16) Γ, Z₀ := thickening (δ / 8) Γ,
    Z_open := isOpen_thickening, Z₀_open := isOpen_thickening,
    circle_mem := self_subset_thickening (by positivity) Γ,
    subset := hZ₀'Z₀, Z_invariant := hth (δ / 16), Z₀_invariant := hth (δ / 8),
    margin := hmargin, root_nonzero := fun z hz => hK₀nz z (hZ₁K (hZ₀Z₁ hz)),
    U := region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁,
    U_open := hregion, U_subset := hUsub,
    tube := label_regular m N ψ hZ₀Z₁ hρR₁ (fun z hz => hK₀u z (hZ₁K hz))
      (fun z hz ξ hξ => hnzZ₁ z (subset_closure hz) ξ hξ.le),
    disjoint := hdisr,
    fixed := Finsler.RootFlowFixed.descent_fixed hL₀ hV00 hg₀ hsupp₀ hle₀ (red m N a) hV₀τ,
    small_strict := hstrictr, value_strict := hψstrict
  }⟩

end

end Finsler.LabelRootData
