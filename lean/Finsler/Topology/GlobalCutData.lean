module

public import Finsler.Topology.CoreLocal
public import Finsler.Topology.SmallLevel
public import Finsler.Topology.FixedCrossingSupport

/-! Extend the large-cut global hypotheses to all real cuts,
with explicit larger filling and resonance margins. -/

@[expose] public section

namespace Finsler.GlobalCutData

open Set Module Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1000000

variable {n : ℕ} (F : ReversibleMetric n)

theorem cut_res {a b : ℝ} (hab : a ≤ b) (q : ℕ) (x : H (fullComplex n) q) :
    Hmap (cutHom F hab) q (Hmap (resHom F b) q x) = Hmap (resHom F a) q x := by
  rw [← Hmap_comp]
  exact Hmap_congr (cut_res_f F hab) q x

theorem cut_cut {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (q : ℕ)
    (x : H (levComplex F c) q) :
    Hmap (cutHom F hab) q (Hmap (cutHom F hbc) q x) =
      Hmap (cutHom F (hab.trans hbc)) q x := by
  exact (Finsler.OrdinaryRestriction.Hmap_cut_cut F hab hbc q x).symm

theorem H_lev_nonpos {a : ℝ} (ha : a ≤ 0) (q : ℕ) (x : H (levComplex F a) q) : x = 0 :=
  Finsler.FixedCrossingSupport.H_eq_zero_of_HR (levComplex F a) q
    (Finsler.SmallLevel.HR_lev_eq_zero_of_nonpos F ha q) x

theorem filling_all {a₀ D : ℝ} (ha₀ : 0 < a₀) (hD : 0 ≤ D)
    (fill : ∀ a b : ℝ, ∀ hab : a ≤ b, a₀ ≤ a → a + D ≤ b → ∀ q (y : H (levComplex F b) q),
      ∃ x : H (fullComplex n) q, Hmap (resHom F a) q x = Hmap (cutHom F hab) q y) :
    ∀ a b : ℝ, ∀ hgap : a + (D + a₀) ≤ b, ∀ q (y : H (levComplex F b) q),
      ∃ x : H (fullComplex n) q, Hmap (resHom F a) q x =
        Hmap (cutHom F (by linarith : a ≤ b)) q y := by
  intro a b hgap q y
  by_cases ha : 0 < a
  · by_cases hlarge : a₀ ≤ a
    · exact fill a b (by linarith) hlarge (by linarith) q y
    · have haa₀ : a ≤ a₀ := le_of_lt (not_le.mp hlarge)
      have ha₀b : a₀ ≤ b := by linarith
      obtain ⟨x, hx⟩ := fill a₀ b ha₀b le_rfl (by linarith) q y
      refine ⟨x, ?_⟩
      rw [← cut_res F haa₀, hx, cut_cut F haa₀ ha₀b]
  · refine ⟨0, ?_⟩
    rw [map_zero]
    exact (H_lev_nonpos F (not_lt.mp ha) q _).symm

theorem ordinary_inj_all {a₀ α C : ℝ} (ha₀ : 0 < a₀) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hinj : ∀ a : ℝ, a₀ ≤ a → ∀ q : ℕ, C < (q : ℝ) → (q : ℝ) < α * a - C →
      Function.Injective (Hmap (resHom F a) q))
    {Q : ℕ} (hQ : C < (Q : ℝ)) :
    ∀ a : ℝ, ∀ q : ℕ, Q ≤ q → (q : ℝ) < α * a - (C + α * a₀) →
      Function.Injective (Hmap (resHom F a) q) := by
  intro a q hq hband
  have hqR : (Q : ℝ) ≤ q := by exact_mod_cast hq
  have hαa₀ : 0 ≤ α * a₀ := mul_nonneg hα ha₀.le
  have hlarge : a₀ ≤ a := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_left (not_le.mp h).le hα
    have hzero : (0 : ℝ) ≤ q := by positivity
    linarith
  exact hinj a hlarge q (hQ.trans_le hqR) (by linarith)

theorem ordinary_zero_all {a₀ α C : ℝ} (ha₀ : 0 < a₀) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hzero : ∀ a : ℝ, a₀ ≤ a → ∀ q : ℕ, α * a + C < (q : ℝ) →
      ∀ x : H (fullComplex n) q, Hmap (resHom F a) q x = 0) :
    ∀ a : ℝ, ∀ q : ℕ, α * a + (C + α * a₀) < (q : ℝ) →
      ∀ x : H (fullComplex n) q, Hmap (resHom F a) q x = 0 := by
  intro a q hq x
  by_cases ha : 0 < a
  · by_cases hlarge : a₀ ≤ a
    · exact hzero a hlarge q (by nlinarith) x
    · have hαa : 0 ≤ α * a := mul_nonneg hα ha.le
      have hx := hzero a₀ le_rfl q (by linarith) x
      rw [← cut_res F (le_of_lt (not_le.mp hlarge)), hx, map_zero]
  · exact H_lev_nonpos F (not_lt.mp ha) q _

end

end Finsler.GlobalCutData
