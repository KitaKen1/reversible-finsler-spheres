module

public import Finsler.Topology.GlobalCutData

/-! Derive the reflection detection band from large-cut filling,
ordinary resonance and global w-nilpotence, with explicit larger margins. -/

@[expose] public section

namespace Finsler.GlobalDetection

open Set Module Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.NilpotentW

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1000000

theorem wPow_zero_of_le (K : InvComplex) {N M : ℕ} (hNM : N ≤ M)
    (h : ∀ lo (x : HR K lo), wPow K lo N x = 0) :
    ∀ lo (x : HR K lo), wPow K lo M x = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hNM
  clear hNM
  induction t with
  | zero => simpa only [Nat.add_zero] using h
  | succ t ih =>
    intro lo x
    rw [Nat.add_succ, wPow_succ, ih, map_zero]

theorem exists_detection {n : ℕ} (F : ReversibleMetric n) {N : ℕ}
    (hnil : ∀ lo (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0)
    {a₀ α C D : ℝ} (ha₀ : 0 < a₀) (hα : 0 ≤ α) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (fill : ∀ a b : ℝ, ∀ hab : a ≤ b, a₀ ≤ a → a + D ≤ b → ∀ q (y : H (levComplex F b) q),
      ∃ x : H (fullComplex n) q, Hmap (resHom F a) q x = Hmap (cutHom F hab) q y)
    (hinj : ∀ a : ℝ, a₀ ≤ a → ∀ q : ℕ, C < (q : ℝ) → (q : ℝ) < α * a - C →
      Function.Injective (Hmap (resHom F a) q))
    (hzero : ∀ a : ℝ, a₀ ≤ a → ∀ q : ℕ, α * a + C < (q : ℝ) →
      ∀ x : H (fullComplex n) q, Hmap (resHom F a) q x = 0) :
    ∃ C' : ℝ, ∃ q₀ : ℕ,
      (∀ q a, q₀ ≤ q → 0 < a → (q : ℝ) < α * a - C' →
        Function.Injective (HRmap (resHom F a) q)) ∧
      (∀ q a, q₀ ≤ q → 0 < a → α * a + C' < (q : ℝ) →
        ∀ x, HRmap (resHom F a) q x = 0) := by
  obtain ⟨J, hJ⟩ := exists_nat_gt C
  let N' := N + J
  have hQ : C < ((N' + 3 : ℕ) : ℝ) := by
    have hle : J ≤ N' + 3 := by dsimp [N']; omega
    exact hJ.trans_le (Nat.cast_le.mpr hle)
  have hnil' : ∀ lo (x : HR (fullComplex n) lo), wPow (fullComplex n) lo (N' + 1) x = 0 :=
    wPow_zero_of_le (fullComplex n) (by dsimp [N']; omega) hnil
  obtain ⟨hi, hz⟩ := Finsler.EndgameAssembly.detection_actual F α (D + a₀) (C + α * a₀)
    (by linarith) N'
    (Finsler.GlobalCutData.filling_all F ha₀ hD fill)
    (Finsler.GlobalCutData.ordinary_inj_all F ha₀ hα hC hinj hQ)
    (fun a q _ hq => Finsler.GlobalCutData.ordinary_zero_all F ha₀ hα hC hzero a q hq)
    hnil'
  exact ⟨(C + α * a₀) + α * (N' : ℝ) * (D + a₀), 2 * (N' + 1) + 1,
    (fun q a hq _ h => hi q a hq h), (fun q a hq _ h => hz q a hq h)⟩

end

end Finsler.GlobalDetection
