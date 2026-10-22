module

public import Finsler.Geometry.RoundThom
public import Finsler.Topology.LensCore

/-! The lens pairs of the model of the regular m-gons.

For cuts a ≤ (2πm)² < c the lens theorem for cone structures and the Thom pair give: the lens
pair of the whole model space has the cohomology of V₂ shifted by l = (2m − 1)(n − 1) and none
below l. For tight cuts (2(c − a') ≤ ρ², T ≥ 1) every point below c which the flow does not take
to a' or below lies in the label set 𝒲_ρ = {sqN < ρ², sqP < ρ²}, so the lens pairs in 𝒲_ρ and in
the whole space have the same cohomology (`LensCore`); and points of 𝒲_ρ below c which are not
taken below a stay in 𝒲_ρ up to the time T. -/

@[expose] public section

namespace Finsler.RoundModelLens

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundCoords Finsler.RoundSpectral Finsler.RoundModes Finsler.AmbientPenalty
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundLabel Finsler.RoundModel
open Finsler.RoundCone Finsler.RoundThom Finsler.ConeLens Finsler.FlowLens
open Finsler.LensContinuation Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Module
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)

theorem flowM_sqN (t : ℝ) (w : MS n N m) :
    sqN ((descentM hm hmN).flow t w).1 = Real.exp t ^ 2 * sqN w.1 :=
  sqN_scale hm hmN w.2 w.1.2 _

theorem flowM_sqP (t : ℝ) (w : MS n N m) :
    sqP ((descentM hm hmN).flow t w).1 = Real.exp (-t) ^ 2 * sqP w.1 :=
  sqP_scale hm hmN w.2 w.1.2 _ _

theorem energy_flowM (t : ℝ) (w : MS n N m) :
    (cone hm hmN).energy ((descentM hm hmN).flow t w) =
      (2 * π * m) ^ 2 - Real.exp t ^ 2 * sqN w.1 + Real.exp (-t) ^ 2 * sqP w.1 := by
  rw [cone_energy, model, flowM_sqN, flowM_sqP]

/-! ### The lens pair of the whole model -/

variable {a c T : ℝ} (ha : a ≤ (2 * π * m) ^ 2) (hc : (2 * π * m) ^ 2 < c) (hT : 0 ≤ T)

include ha hc hT in
/-- **The lens pair of the whole model.** -/
theorem model_lens_finrank (hn : 1 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (H (triv (pairOf
      (setY_sub_setU (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T)))
        (k + (2 * m - 1) * (n - 1))) =
      finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k) := by
  rw [(coneEquiv (split hm hmN) isOpen_univ (fun _ _ _ _ _ _ => mem_univ _)
    (fun _ _ _ _ _ _ _ => mem_univ _) (s₀ := 0) (fun _ _ _ _ _ => hc) hT le_rfl _).finrank_eq]
  exact thom_finrank hm hmN ha hc hn k

include ha hc hT in
theorem model_lens_zero (hn : 1 ≤ n) (q : ℕ) (hq : q < (2 * m - 1) * (n - 1))
    (x : H (triv (pairOf
      (setY_sub_setU (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T))) q) :
    x = 0 := by
  let e := coneEquiv (split (n := n) hm hmN) (𝒲 := univ) (a := a) (b := c) (T := T) isOpen_univ
    (fun _ _ _ _ _ _ => mem_univ _) (fun _ _ _ _ _ _ _ => mem_univ _) (s₀ := 0)
    (fun _ _ _ _ _ => hc) hT le_rfl q
  have h0 : e x = 0 := thom_zero hm hmN ha hc hn q hq (e x)
  exact (LinearEquiv.map_eq_zero_iff e).mp h0

include ha hc hT in
theorem model_lens_finite (hn : 1 ≤ n) (k : ℕ)
    (hk : Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k)) :
    Module.Finite (ZMod 2) (H (triv (pairOf
      (setY_sub_setU (cone hm hmN) (descentM hm hmN) (univ : Set (MS n N m)) a c T)))
        (k + (2 * m - 1) * (n - 1))) := by
  haveI := thom_finite hm hmN ha hc (T := T) hn k hk
  exact Module.Finite.equiv (coneEquiv (split (n := n) hm hmN) (𝒲 := univ) (a := a) (b := c)
    (T := T) isOpen_univ (fun _ _ _ _ _ _ => mem_univ _) (fun _ _ _ _ _ _ _ => mem_univ _)
    (s₀ := 0) (fun _ _ _ _ _ => hc) hT le_rfl _).symm

/-! ### The label set of the model -/

/-- The label set of the model. -/
def labelM (ρ : ℝ) : Set (MS n N m) := {w | sqN w.1 < ρ ^ 2 ∧ sqP w.1 < ρ ^ 2}

theorem labelM_isOpen (ρ : ℝ) : IsOpen (labelM (n := n) (N := N) (m := m) ρ) := by
  have h1 : Continuous fun w : MS n N m => sqN w.1 :=
    (sqN_contDiff (n := n) (N := N) (m := m)).continuous.comp continuous_subtype_val
  have h2 : Continuous fun w : MS n N m => sqP w.1 :=
    (sqP_contDiff (n := n) (N := N) (m := m)).continuous.comp continuous_subtype_val
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)

/-- Points below c which are not taken to a' or below in time T ≥ 1 have small negative and
positive parts. -/
theorem core_small {a' : ℝ} (hc' : (2 * π * m) ^ 2 ≤ c) (ha' : a' ≤ (2 * π * m) ^ 2)
    (hT1 : 1 ≤ T) (w : MS n N m) (hw : (cone hm hmN).energy w < c)
    (hw' : a' < (cone hm hmN).energy ((descentM hm hmN).flow T w)) :
    sqN w.1 ≤ c - a' ∧ sqP w.1 ≤ 2 * (c - a') := by
  rw [cone_energy] at hw
  rw [energy_flowM] at hw'
  unfold model at hw
  have hN := sqN_nonneg w.1
  have hP := sqP_nonneg w.1
  have he1 : 2 ≤ Real.exp T ^ 2 := by
    have : Real.exp 1 ≤ Real.exp T := Real.exp_le_exp.mpr hT1
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    nlinarith
  have he2 : Real.exp (-T) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
  have he3 : 0 ≤ Real.exp (-T) ^ 2 := sq_nonneg _
  have h1 : Real.exp T ^ 2 * sqN w.1 ≤ (c - a') + sqN w.1 := by nlinarith
  have hsN : sqN w.1 ≤ c - a' := by nlinarith
  exact ⟨hsN, by linarith⟩

theorem core_mem {a' ρ : ℝ} (hc' : (2 * π * m) ^ 2 ≤ c) (ha' : a' ≤ (2 * π * m) ^ 2)
    (hT1 : 1 ≤ T) (hρ : 4 * (c - a') < ρ ^ 2) (w : MS n N m) (hw : (cone hm hmN).energy w < c)
    (hw' : a' < (cone hm hmN).energy ((descentM hm hmN).flow T w)) : w ∈ labelM ρ := by
  obtain ⟨h1, h2⟩ := core_small hm hmN hc' ha' hT1 w hw hw'
  have hca : 0 ≤ c - a' := by linarith
  exact ⟨by linarith, by linarith⟩

/-- **The lens pairs of the label set and of the whole model agree** for tight cuts. -/
theorem nonempty_label_equiv {a' ρ : ℝ} (ha'a : a' < a) (hc' : (2 * π * m) ^ 2 ≤ c)
    (ha' : a' ≤ (2 * π * m) ^ 2) (hT1 : 1 ≤ T) (hρ : 4 * (c - a') < ρ ^ 2) (q : ℕ) :
    Nonempty (H (triv (pairOf (partY_sub_partU (cone hm hmN).energy (descentM hm hmN)
        (labelM (n := n) (N := N) (m := m) ρ) a c T))) q ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU (cone hm hmN).energy (descentM hm hmN)
        (univ : Set (MS n N m)) a c T))) q) :=
  Finsler.LensCore.nonempty_core_equiv (descentM hm hmN) (energy_continuous (cone hm hmN)) ha'a
    (fun w hw hw' => ⟨fun _ => mem_univ _,
      fun _ => core_mem hm hmN hc' ha' hT1 hρ w hw hw'⟩) q

/-- **Trapping in the model.** Points of the label set below c which the flow does not take below
a in time T stay in the label set up to the time T. -/
theorem model_trap {ρ : ℝ} (hc' : (2 * π * m) ^ 2 ≤ c) (ha' : a ≤ (2 * π * m) ^ 2)
    (hT1 : 1 ≤ T) (hρ : 4 * (c - a) < ρ ^ 2) (w : MS n N m) (hw : w ∈ labelM ρ)
    (hwc : (cone hm hmN).energy w < c)
    (hwa : a ≤ (cone hm hmN).energy ((descentM hm hmN).flow T w)) (s : ℝ) (hs : 0 ≤ s)
    (hsT : s ≤ T) : (descentM hm hmN).flow s w ∈ labelM ρ := by
  have hwa' : a - 1 < (cone hm hmN).energy ((descentM hm hmN).flow T w) := by linarith
  obtain ⟨h1, -⟩ := core_small hm hmN hc' (by linarith) hT1 w hwc hwa'
  -- a sharper bound with a itself
  rw [cone_energy] at hwc
  rw [energy_flowM] at hwa
  unfold model at hwc
  have hN := sqN_nonneg w.1
  have hP := sqP_nonneg w.1
  have heT : Real.exp s ^ 2 ≤ Real.exp T ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le
    (Real.exp_le_exp.mpr hsT) 2
  have he2 : Real.exp (-T) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
  have he3 : 0 ≤ Real.exp (-T) ^ 2 := sq_nonneg _
  have he1 : 2 ≤ Real.exp T ^ 2 := by
    have : Real.exp 1 ≤ Real.exp T := Real.exp_le_exp.mpr hT1
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    nlinarith
  have hbound : Real.exp T ^ 2 * sqN w.1 ≤ 2 * (c - a) := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [flowM_sqN]
    have : Real.exp s ^ 2 * sqN w.1 ≤ Real.exp T ^ 2 * sqN w.1 :=
      mul_le_mul_of_nonneg_right heT hN
    have hca : 0 ≤ c - a := by linarith
    linarith
  · rw [flowM_sqP]
    have hes : Real.exp (-s) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by linarith))
    have : Real.exp (-s) ^ 2 * sqP w.1 ≤ sqP w.1 := by nlinarith
    exact lt_of_le_of_lt this hw.2

end

end Finsler.RoundModelLens
