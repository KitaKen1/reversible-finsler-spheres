module

public import Finsler.Geometry.RoundLevel
public import Finsler.Geometry.ECupTransport
public import Finsler.Geometry.LevelCrossingCup

/-! The evaluation class on the round polygon crossings (Claude prototype).

The label data of `RoundLevel.round_level` with `LevelCrossingCup.level_crossing_cup` and
`ECupTransport.crossing_lens_cup`: if the cup with π^*[Sⁿ] is injective on H⁰(V₂), the cup with
the evaluation class of the ambient polygons annihilates no nonzero class of the crossing pair of
the penalized energy at the level (2πm)² in the degree (2m − 1)(n − 1). -/

@[expose] public section

namespace Finsler.RoundLevelCup

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundCoords Finsler.RoundSpectral Finsler.RoundModes Finsler.AmbientPenalty
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundLabel Finsler.RoundModel Finsler.RoundQR
open Finsler.RoundCone Finsler.RoundThom Finsler.RoundModelLens Finsler.RoundTransport
open Finsler.RoundDeform Finsler.RoundPenHess Finsler.LogCutoff Finsler.PolygonSmooth
open Finsler.LevelField Finsler.LevelCrossingFin Finsler.LensFamily Finsler.PolygonDescent
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.EnergySphereSmooth
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LensContinuation Finsler.AmbientDescent Module
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff NNReal

open Finsler.RoundLevel Finsler.ECup Finsler.ECupThom Finsler.ECupTransport
open Finsler.LevelCrossingCup

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The evaluation class on the round polygon crossings.** -/
theorem round_level_cup (hn : 1 ≤ n) {M : ℕ} (hNM : N = 2 * M + 1) (hm : 0 < m) (hmM : m < M)
    {δ : ℝ} (hδ2 : δ ≤ 2)
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy (roundMetric n)) ((P : Ambient n), (Q : Ambient n)))
    {a b : ℝ} (ha : 0 < a) (hlo : (2 * π * ((m : ℝ) - 1)) ^ 2 < a) (hac : a < (2 * π * m) ^ 2)
    (hcb : (2 * π * m) ^ 2 < b) (hhi : b < (2 * π * ((m : ℝ) + 1)) ^ 2)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy (roundMetric n) N q ≤ b →
      ShortPolygon δ q)
    (hV : CupInjW (eV n hn) (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) 0)
    (hab : a ≤ b) :
    CupInjW (eOm n N hn) (sub_mono (penW (roundMetric n) N 1) hab) ((2 * m - 1) * (n - 1)) := by
  have hmN := two_m_lt_N hNM hmM
  obtain ⟨R_S, cS, hRS, hcS, hS⟩ := exists_split_descent (n := n) hNM hm hmM
  obtain ⟨R_D, cD, lam, hRD, hcD, hlam, hD⟩ := exists_deform_descent (n := n) hNM hm hmM
  obtain ⟨R_Q, C_Q, hRQ, hCQ, hQ⟩ := exists_quadratic (n := n) hNM hm hmM
  obtain ⟨cF, CF, hcF, hCF, hF⟩ := exists_sqF_bounds (n := n) (N := N) (m := m)
  -- the radius
  set R₀ := min (min R_S R_D) (min R_Q (1 / 2)) with hR₀def
  have hR₀ : 0 < R₀ := lt_min (lt_min hRS hRD) (lt_min hRQ (by norm_num))
  have hR₀1 : R₀ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hR₀S : R₀ ≤ R_S := (min_le_left _ _).trans (min_le_left _ _)
  have hR₀D : R₀ ≤ R_D := (min_le_left _ _).trans (min_le_right _ _)
  have hR₀Q : R₀ ≤ R_Q := (min_le_right _ _).trans (min_le_left _ _)
  have hS' : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ → (z, ξ) ∈ dom (n := n) (N := N) m ∧
      fderiv ℝ (Psi (n := n) (N := N) m) (z, ξ) (0, J hm hmN z ξ) ≤ -cS * ‖ξ‖ ^ 2 :=
    fun z hz ξ hξ => hS z hz ξ (hξ.trans hR₀S)
  have hQ' : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ →
      |Psi (n := n) (N := N) m (z, ξ) - (2 * π * m) ^ 2| ≤ C_Q * ‖ξ‖ ^ 2 :=
    fun z hz ξ hξ => (hQ z hz ξ (hξ.trans hR₀Q)).2
  have hsqF : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, cF * ‖ξ‖ ^ 2 ≤ sqF (z, ξ) :=
    fun z hz ξ => (hF z hz ξ).1
  -- the comparison of the model with Ψ
  set C₁ := 1 + C_Q / cF with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hMΨ : ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m, ‖ξ‖ ≤ R₀ →
      |model m (z, ξ) - Psi (n := n) (N := N) m (z, ξ)| ≤ C₁ * sqF (z, ξ) := by
    intro z hz ξ hξ
    have h1 : |model m (z, ξ) - (2 * π * m) ^ 2| ≤ sqF (z, ξ) := by
      unfold model sqF
      rw [show (2 * π * m) ^ 2 - sqN (z, ξ) + sqP (z, ξ) - (2 * π * m) ^ 2 =
        sqP (z, ξ) - sqN (z, ξ) by ring, abs_le]
      have := sqN_nonneg (z, ξ)
      have := sqP_nonneg (z, ξ)
      constructor <;> linarith
    have h2 : C_Q * ‖ξ‖ ^ 2 ≤ C_Q / cF * sqF (z, ξ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcF]
      nlinarith [hsqF z hz ξ]
    have hq := hQ' z hz ξ hξ
    calc |model m (z, ξ) - Psi (n := n) (N := N) m (z, ξ)|
        = |(model m (z, ξ) - (2 * π * m) ^ 2) - (Psi m (z, ξ) - (2 * π * m) ^ 2)| := by ring_nf
      _ ≤ |model m (z, ξ) - (2 * π * m) ^ 2| + |Psi m (z, ξ) - (2 * π * m) ^ 2| := abs_sub _ _
      _ ≤ sqF (z, ξ) + C_Q / cF * sqF (z, ξ) := add_le_add h1 (hq.trans h2)
      _ = C₁ * sqF (z, ξ) := by rw [hC₁def]; ring
  -- the size of the piece
  set δw := min ((2 * π * m) ^ 2 - a) (b - (2 * π * m) ^ 2) with hδwdef
  have hδw : 0 < δw := lt_min (by linarith) (by linarith)
  set sT := min (cF * R₀ ^ 2 / 4) (δw / (2 * (C_Q / cF + C₁ + 1))) with hsTdef
  have hsT0 : 0 < sT := lt_min (by positivity) (by positivity)
  have hsT : sT ≤ cF * R₀ ^ 2 / 4 := min_le_left _ _
  have hsTw : (C_Q / cF + C₁) * sT < δw := by
    have h1 : sT ≤ δw / (2 * (C_Q / cF + C₁ + 1)) := min_le_right _ _
    have h2 : 0 ≤ C_Q / cF := by positivity
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hη : C_Q / cF * sT + C₁ * sT < (2 * π * m) ^ 2 - a := by
    have := min_le_left ((2 * π * m) ^ 2 - a) (b - (2 * π * m) ^ 2)
    nlinarith
  have hη' : C_Q / cF * sT + C₁ * sT < b - (2 * π * m) ^ 2 := by
    have := min_le_right ((2 * π * m) ^ 2 - a) (b - (2 * π * m) ^ 2)
    nlinarith
  -- the cutoff radius
  set r := Real.sqrt (sT * Real.exp (-lam)) with hrdef
  have hr2 : r ^ 2 = sT * Real.exp (-lam) := Real.sq_sqrt (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr : r ≠ 0 := hr0.ne'
  have hrs : r ^ 2 * Real.exp lam ≤ sT := by
    rw [hr2, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hr2s : r ^ 2 ≤ sT := by
    rw [hr2]
    exact mul_le_of_le_one_right hsT0.le (Real.exp_le_one_iff.mpr (by linarith))
  -- the label radii
  set ρ := min 1 (r / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρr : 2 * ρ ^ 2 ≤ r ^ 2 := by
    have h : ρ ≤ r / 2 := min_le_right _ _
    have h' : ρ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ hρ0.le h 2
    nlinarith
  have hρs : 2 * ρ ^ 2 ≤ sT := hρr.trans hr2s
  set ρ' := ρ / Real.exp 1 with hρ'def
  have hρ'0 : 0 < ρ' := div_pos hρ0 (Real.exp_pos 1)
  have hρρ' : Real.exp 1 * ρ' ≤ ρ := by
    rw [hρ'def, mul_div_cancel₀ _ (Real.exp_pos 1).ne']
  have hsmall : Small n N m ρ := small_of hm hmN hR₀ hcF hsqF hsT hS' hρ0 hρ1 hρs
  -- the compact piece
  have hTc : IsCompact (Tset (n := n) (N := N) m sT) := Tset_isCompact hR₀ hcF hsqF hsT
  have hTU : Tset (n := n) (N := N) m sT ⊆ Uset hm hmN R₀ :=
    Tset_subset hm hmN hR₀ hR₀1 hcF hsqF hsT
  have hgood : ∀ y ∈ Uset (n := n) (N := N) hm hmN R₀, y ∈ good N :=
    fun y hy => Uset_good hm hmN hS' hy
  -- the descent of the deformed energy on the piece
  have hβ : ∀ y ∈ tsupport (βf (n := n) (N := N) hm hmN r lam),
      fderiv ℝ (fun y => pen (roundMetric n) N 1 y + βf hm hmN r lam y) y (fieldW hm hmN y) ≤
        -cD * sqF (unchart hm hmN y) := by
    intro y hy
    have hyT := tsupport_βf_subset hm hmN hr hlam hrs hTc.isClosed hy
    obtain ⟨hg, ⟨hz, hsq⟩, hξ, -⟩ := mem_Tset hm hmN hR₀ hR₀1 hcF hsqF hsT hyT
    have hξD : ‖(unchart hm hmN y).2‖ ≤ R_D := hξ.trans (by linarith)
    obtain ⟨hdom, -, hG⟩ := hD r lam hr le_rfl _ hz _ hξD
    simp only [Prod.mk.eta] at hdom hG
    rw [fderiv_penβ hm hmN hr hlam hrs (by linarith) hTU hTc.isClosed hgood hyT hdom]
    exact hG
  -- the crossing of the level
  exact level_crossing_cup (roundMetric n) hn hδ (a₀ := a) (b₀ := b) hshort
    (U := Uset hm hmN R₀) (W := fieldW hm hmN) (β := βf hm hmN r lam) (C := Cset hm hmN)
    (T := Tset m sT) (𝒲 := labO hm hmN ρ) (𝒲' := labO hm hmN ρ')
    (Uset_isOpen hm hmN R₀) (Uset_reg hm hmN hS')
    (fun y hy => (fieldW_contDiffAt hm hmN hy.1).contDiffWithinAt)
    (fun y hy => W_nonpos hm hmN hcS hS' hy) (fun y hy hC => W_neg hm hmN hcS hS' hy hC)
    hTc hTU (tsupport_βf_subset hm hmN hr hlam hrs hTc.isClosed)
    (fun y => βf_differentiableAt hm hmN hr hlam hrs hTU hTc.isClosed hgood y)
    (fun y hy => (hβ y hy).trans (by
      have := sqF_nonneg (unchart hm hmN y)
      nlinarith))
    (fun y hy hC => (hβ y hy).trans_lt (by
      have hyT := tsupport_βf_subset hm hmN hr hlam hrs hTc.isClosed hy
      have hg := (hTU hyT).1
      have hne : (unchart hm hmN y).2 ≠ 0 := fun h0 => hC ⟨hg, h0⟩
      have hpos : 0 < sqF ((unchart hm hmN y).1, (unchart hm hmN y).2) := sqF_pos _ hne
      simp only [Prod.mk.eta] at hpos
      nlinarith))
    (labO_isOpen hm hmN ρ)
    (fun Q hQ => labA_mono hm hmN hρ'0.le (hρρ'.trans' (le_mul_of_one_le_left hρ'0.le
      (Real.one_le_exp zero_le_one))) hQ)
    (fun Q hQ => labA_sub_Tset hm hmN hρs hQ) (fun Q hQ => Cset_sub_labO hm hmN hρ'0 Q hQ)
    (Cset_subset hm hmN hR₀) (c₀ := (2 * π * m) ^ 2)
    (fun y hy => Cset_val hm hmN hR₀ hQ' hy r lam) (η := C₁ * sT)
    (fun y => βf_bound hm hmN hR₀ hR₀1 hcF hsqF hsT hr hlam hrs hC₁ hMΨ y)
    (aw := a) (bw := b) le_rfl le_rfl hac hcb
    (fun y hy => Tset_val hm hmN hR₀ hR₀1 hcF hsqF hsT hCQ hQ' hη hη' hy)
    (fun q hq1 hq2 hqc => crit_mem_Tset hδ2 ha hlo hhi hsT0.le q hq1 hq2 (hshort q hq2) hqc)
    (eOm n N hn) ((2 * m - 1) * (n - 1))
    (fun {V} {KL} hL hV0 {g} {O} hg hsupp hle hVT hgT {a₀a} {b₀a} ha₀a hb₀a hgc hK {R} hR
        hdis hstrict => by
      obtain ⟨d, hd, h⟩ := crossing_lens_cup hm hmN hL hV0 hg hsupp hle hn hsmall hρ'0 hρρ'
        (fun Q hQ => hVT Q (labA_sub_Tset hm hmN hρs hQ))
        (fun Q hQ => (hgT Q (labA_sub_Tset hm hmN hρs hQ)).trans
          (penβ_labA hm hmN hr hlam hρr hQ))
        ha₀a hb₀a hgc hK hR hdis hstrict
      exact ⟨d, hd, fun a c t ht ha hc hca => h a c t ht ha hc hca hV⟩)
    hab

end

end Finsler.RoundLevelCup
