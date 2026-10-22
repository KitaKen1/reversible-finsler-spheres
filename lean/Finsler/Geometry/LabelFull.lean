module

public import Finsler.Geometry.LabelLevel
public import Finsler.Geometry.AmbientTrap
public import Finsler.Geometry.RootTrap

/-! A label of the deformed energy is the shifted root label, with all trapping hypotheses
discharged. Let the global field of a level agree with the ambient split field of a label on its
tube, and the deformed energy with the deformed energy of the label there. Let the label sets
be the ambient label sets over Z₀' ⊆ Z₀ ⊆ Z₁ with radii ρ' e ≤ ρ ≤ R₁, 2ρ² ≤ r² (so the cutoff is
1 on them), and let the root field be bounded by κ' with Z₀' + (κ'-ball) ⊆ Z₀. If the deformed
energy decreases strictly along the global descent on a compact band outside the small label
set and an open set R disjoint from the large one, and the root descent decreases the root
functional strictly on a compact root band outside {z ∈ Z₀'} and an open set disjoint from Z₀,
then for all sufficiently tight cuts (and the strip condition of the normal shift) the lens pair
of the label has in degree k + b the dimension of the root lens pair in Z₀ in degree k, and no
cohomology below b. -/

@[expose] public section

namespace Finsler.LabelFull

open Module Filter Set Metric CategoryTheory
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform Finsler.LabelTransport
open Finsler.LabelRegions Finsler.AmbientDescent Finsler.FlowLens Finsler.ProductModel
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LensContinuation
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n) (F : ReversibleMetric n)
  {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : ℝ≥0} (hL : LipschitzWith K V)
  (hV0 : ∀ P : ZMod (m * N) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod (m * N) → Ambient n) → ℝ} {O : Set (ZMod (m * N) → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)
  {K₀' : ℝ≥0} (hL₀ : LipschitzWith K₀' V₀)
  (hV00 : ∀ z : ZMod N → Ambient n, V₀ z ≠ 0 → ∀ j, z j ≠ 0)
  {O₀ : Set (ZMod N → Ambient n)}
  (hg₀ : ∀ z ∈ O₀, DifferentiableAt ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z)
  (hsupp₀ : ∀ z, V₀ z ≠ 0 → z ∈ O₀)
  (hle₀ : ∀ z ∈ O₀, fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z (V₀ z) ≤ 0)
  (hh : Continuous fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)

include hh in
/-- **A label is the shifted root label.** -/
theorem label_full (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₁ Z₀ Z₀' : Set (ZMod N → Ambient n)} {R₁ ρ ρ' κ' r : ℝ}
    {χ₀ : (ZMod N → Ambient n) → ℝ} {lam : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (hZ₁o : IsOpen Z₁) (hZ₁u : ∀ z ∈ Z₁, IsUnit (matA m N G₁ G₂ ψ z))
    (hnz : ∀ z ∈ Z₁, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ < R₁ →
      ∀ j, coord m N G₁ G₂ (z, ξ) j ≠ 0)
    (hZ₀o : IsOpen Z₀) (hZ₀'o : IsOpen Z₀') (hZ₀Z₁ : Z₀ ⊆ Z₁) (hZ₀'Z₀ : Z₀' ⊆ Z₀)
    (hZ₀nz : ∀ z ∈ Z₀, ∀ j, z j ≠ 0) (hχ1 : ∀ z ∈ Z₀, χ₀ z = 1)
    (hρ0 : 0 < ρ) (hρR : ρ ≤ R₁) (hρr : 2 * ρ ^ 2 ≤ r ^ 2) (hρ' : ρ' * Real.exp 1 ≤ ρ)
    (hV₀b : ∀ z, ‖V₀ z‖ ≤ κ') (hmargin : ∀ z ∈ Z₀', ∀ z', ‖z' - z‖ ≤ κ' → z' ∈ Z₀)
    (hVT : ∀ y ∈ region m N G₁ G₂ ψ Z₁ R₁, V y = splitW m N G₁ G₂ ψ V₀ y)
    (hgT : ∀ y ∈ region m N G₁ G₂ ψ Z₁ R₁, g y = gDef m N F G₁ G₂ ψ χ₀ r lam y)
    -- the ambient band
    {a₀ b₀ : ℝ} (hgc : Continuous fun Q : Om n (m * N) => g Q.1)
    (hK : IsCompact {Q : Om n (m * N) | a₀ ≤ g Q.1 ∧ g Q.1 ≤ b₀})
    {Ramb : Set (Om n (m * N))} (hRamb : IsOpen Ramb)
    (hdisa : Disjoint (labelSetA m N G₁ G₂ ψ Z₀ (region m N G₁ G₂ ψ Z₁ R₁) ρ) Ramb)
    (hstricta : ∀ Q : Om n (m * N), a₀ ≤ g Q.1 → g Q.1 ≤ b₀ →
      Q ∉ labelSetA m N G₁ G₂ ψ Z₀' (region m N G₁ G₂ ψ Z₁ R₁) ρ' ∪ Ramb →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1)
    -- the root band
    {a₀r b₀r : ℝ}
    (hKr : IsCompact {z : Om n N | a₀r ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀r})
    {Wrest : Set (Om n N)} (hWrest : IsOpen Wrest)
    (hdisr : Disjoint {z : Om n N | z.1 ∈ Z₀} Wrest)
    (hstrictr : ∀ z : Om n N, a₀r ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀r → z ∉ {z : Om n N | z.1 ∈ Z₀'} ∪ Wrest →
      (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c T : ℝ, 1 ≤ T → a ≤ c → 4 * (c - a) < ρ ^ 2 → 2 * (c - a) < d →
      a₀ ≤ a → c ≤ b₀ →
      a₀r ≤ a - (c - a) / (Real.exp (2 * T) - 1) → c + (c - a) / (Real.exp (2 * T) - 1) ≤ b₀r →
      (∀ z : Om n N, c ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ c + (c - a) / (Real.exp (2 * T) - 1) →
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
          (m : ℝ) ^ 2 * pen F N (1 / m) z.1) →
      (∀ k : ℕ, Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
          (fun Q : Om n (m * N) => g Q.1) (descentOf hL hV0 hg hsupp hle)
          (labelSetA m N G₁ G₂ ψ Z₀ (region m N G₁ G₂ ψ Z₁ R₁) ρ) a c T))) (k + b)) =
        Module.finrank (ZMod 2) (H (triv (pairOf (inter_subset_left :
          baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1) {z : Om n N | z.1 ∈ Z₀} c ∩
            baseO (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) a T ⊆
          baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)
            {z : Om n N | z.1 ∈ Z₀} c))) k)) ∧
      (∀ k : ℕ, k < b → ∀ x : H (triv (pairOf (partY_sub_partU
          (fun Q : Om n (m * N) => g Q.1) (descentOf hL hV0 hg hsupp hle)
          (labelSetA m N G₁ G₂ ψ Z₀ (region m N G₁ G₂ ψ Z₁ R₁) ρ) a c T))) k, x = 0) := by
  have hregion : IsOpen (region m N G₁ G₂ ψ Z₁ R₁) := region_isOpen m N ψ hG₁ hG₂ hZ₁o R₁
  -- regularity of the label sets
  have hZρ := label_regular m N ψ (G₁ := G₁) (G₂ := G₂) hZ₀Z₁ hρR hZ₁u hnz
  -- the deformed energy is the model on the label set
  have hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ (region m N G₁ G₂ ψ Z₁ R₁) ρ,
      g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1) := by
    rintro Q ⟨hu, hz, hx, hy, hQU⟩
    rw [hgT Q.1 hQU]
    apply gDef_of_cutoff_eq_one m N F G₁ G₂ ψ hu
    apply cutoff_eq_one hr.ne' hlam (hχ1 _ hz)
    have hsq : sqE (cOf m N G₁ G₂ ψ Q.1).2 = ‖eucX (xiOf m N G₁ G₂ ψ Q.1)‖ ^ 2 +
        ‖eucY (xiOf m N G₁ G₂ ψ Q.1)‖ ^ 2 := rfl
    rw [hsq]
    have h1 : ‖eucX (xiOf m N G₁ G₂ ψ Q.1)‖ ^ 2 ≤ ρ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hx.le 2
    have h2 : ‖eucY (xiOf m N G₁ G₂ ψ Q.1)‖ ^ 2 ≤ ρ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy.le 2
    linarith
  have hρρ : ρ' ≤ ρ := by
    have he : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    by_cases hρ'0 : ρ' ≤ 0
    · linarith
    · rw [not_le] at hρ'0
      nlinarith
  have hsel : IsOpen {z : Om n N | z.1 ∈ Z₀} := hZ₀o.preimage continuous_subtype_val
  have hstrictr' : ∀ z : Om n N, a₀r ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀r → z ∉ {z : Om n N | z.1 ∈ Z₀} ∪ Wrest →
      (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
    intro z h1 h2 hz
    refine hstrictr z h1 h2 fun h => hz ?_
    rcases h with h | h
    · exact Or.inl (hZ₀'Z₀ h)
    · exact Or.inr h
  -- the shift, the ambient trapping and the root trapping
  obtain ⟨d₃, hd₃, hshift⟩ := label_shift m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle hL₀ hV00 hg₀
    hsupp₀ hle₀ hh hG₁ hG₂ hZ₀nz hρ0 hZρ hmodel hVT hsel hWrest hdisr hKr hstrictr'
  obtain ⟨d₁, hd₁, htrap₁⟩ := Finsler.AmbientTrap.exists_ambient_trap m N G₁ G₂ ψ V₀ hL hV0 hg
    hsupp hle hL₀ hG₁ hG₂ hZ₀'o hregion hZ₀'Z₀ hρρ hZρ hVT hV₀b hmargin hρ' hRamb hdisa hgc hK
    hstricta
  obtain ⟨d₂, hd₂, htrap₂⟩ := Finsler.RootTrap.exists_trap_bounded hL₀ hV00 hg₀ hsupp₀ hle₀ hV₀b
    (Z := Z₀') (Z₀ := Z₀) (hZ₀'o.preimage continuous_subtype_val) hZ₀'Z₀ hmargin hWrest hdisr hh
    hKr hstrictr
  refine ⟨min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃),
    fun a c T hT hac h4 hd ha₀ hb₀ ha₀r hb₀r hstrip => ?_⟩
  have hd1 : 2 * (c - a) < d₁ := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : 2 * (c - a) < d₂ := lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : 2 * (c - a) < d₃ := lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _))
  have hca : 0 ≤ c - a := sub_nonneg.mpr hac
  -- the widening of the cuts is at most (c - a) / 2
  have hE : 2 ≤ Real.exp (2 * T) - 1 := by
    have h1 : Real.exp 1 ≥ 2 := by
      have := Real.add_one_le_exp 1
      linarith
    have h2 : Real.exp (2 * T) ≥ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith
  have hε : 2 * ((c - a) / (Real.exp (2 * T) - 1)) ≤ c - a := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hwide : (c + (c - a) / (Real.exp (2 * T) - 1)) -
      (a - (c - a) / (Real.exp (2 * T) - 1)) ≤ 2 * (c - a) := by
    linarith
  have hS₁ := fun w hw hwc hwa s hs hsT =>
    htrap₁ a c T ha₀ hb₀ (by linarith) hT w hw hwc hwa s hs hsT
  have hbase := fun z hz h1 h2 s hs hsT =>
    htrap₂ (a - (c - a) / (Real.exp (2 * T) - 1)) (c + (c - a) / (Real.exp (2 * T) - 1)) T ha₀r
      hb₀r (by linarith) hT z hz h1 h2 s hs hsT
  exact hshift a c T hT hac h4 ha₀r hb₀r (by linarith) hstrip hS₁ hbase

end

end Finsler.LabelFull
