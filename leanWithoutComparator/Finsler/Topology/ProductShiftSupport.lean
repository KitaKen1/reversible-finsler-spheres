module

public import Finsler.Topology.ProductShift
public import Finsler.Topology.LensFamily
public import Finsler.Topology.SubspacePairs

/-! Retain the cohomology equivalence of the actual product flow, including finiteness. -/

@[expose] public section

namespace Finsler.ProductShiftSupport

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.ConeLens Finsler.ProductModel Finsler.LensTrap
open Finsler.LensFamily Finsler.LensContinuation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {B : TopCat.{0}} {h : B → ℝ} (ψ : Descent B h) (k : ℕ) (V : Type)
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_equiv (hh : Continuous h) {a₀ b₀ : ℝ} {Wsel Wrest : Set B} (hsel : IsOpen Wsel)
    (hrest : IsOpen Wrest) (hdis : Disjoint Wsel Wrest)
    (hK : IsCompact {z : B | a₀ ≤ h z ∧ h z ≤ b₀})
    (hstrict : ∀ z, a₀ ≤ h z → h z ≤ b₀ → z ∉ Wsel ∪ Wrest → h (ψ.flow 1 z) < h z) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, 1 ≤ T → a ≤ b →
      a₀ ≤ a - (b - a) / (Real.exp (2 * T) - 1) →
      b + (b - a) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (b + (b - a) / (Real.exp (2 * T) - 1)) - (a - (b - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ z, b ≤ h z → h z ≤ b + (b - a) / (Real.exp (2 * T) - 1) → h (ψ.flow 1 z) < h z) →
      (∀ n, Nonempty (
          H (triv (pairOf (inter_subset_left :
            baseP h Wsel b ∩ baseO ψ a T ⊆ baseP h Wsel b))) n ≃ₗ[ZMod 2]
          H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V Wsel)
            a b T))) (n + k))) ∧
      (∀ n, n < k → ∀ z : H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh)
        (over k V Wsel) a b T))) n, z = 0) := by
  obtain ⟨d, hd, htr⟩ := exists_trap ψ hh (hsel.union hrest) hK hstrict
  refine ⟨d, hd, ?_⟩
  intro a b T hT hab ha hb hwidth hstrip
  have hε := Finsler.ProductShift.eps_nonneg hab hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hPT := htr _ _ T ha hb hwidth hT
  have htrap : ∀ z, z ∈ Wsel → h z < b + (b - a) / (Real.exp (2 * T) - 1) →
      a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T z) → ∀ s, 0 ≤ s →
      a - (b - a) / (Real.exp (2 * T) - 1) ≤ h (ψ.flow T (ψ.flow s z)) → ψ.flow s z ∈ Wsel :=
    fun z hz hzb _ s hs hzs => trap_piece ψ hT0.le hsel hrest hdis hPT z hz hzb s hs hzs
  have hKs : IsCompact {z : B | b ≤ h z ∧ h z ≤ b + (b - a) / (Real.exp (2 * T) - 1)} :=
    hK.of_isClosed_subset
      ((isClosed_le continuous_const hh).inter (isClosed_le hh continuous_const))
      (fun z hz => ⟨by linarith [hz.1], hz.2.trans hb⟩)
  obtain ⟨s₀, hs₀, hps⟩ := exists_push ψ hh hKs hstrip
  have hpush : ∀ z, z ∈ Wsel → h z < b + (b - a) / (Real.exp (2 * T) - 1) →
      h (ψ.flow s₀ z) < b := fun z _ hz => hps z hz.le
  exact ⟨fun n => ⟨modelEquiv hh hsel hT0 hs₀ htrap hpush n⟩,
    fun n hn z => model_eq_zero hh hsel hT0 hs₀ htrap hpush n hn z⟩


def baseLensEquiv (U : Set B) (a b T : ℝ) (q : ℕ) :
    lensH ψ U a b T q ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_left : baseP h U b ∩ baseO ψ a T ⊆ baseP h U b))) q := by
  have hY : partY h ψ U a b T = baseP h U b ∩ baseO ψ a T := by
    ext z
    change (h z < b ∧ h (ψ.flow T z) < a ∧ z ∈ U) ↔
      ((h z < b ∧ z ∈ U) ∧ h (ψ.flow T z) < a)
    tauto
  exact Finsler.SubspacePairs.equalHEquiv hY rfl _ _ q

theorem support_of_shift (hh : Continuous h) (U : Set B) (a b T : ℝ) (A : ℕ)
    (he : ∀ q, Nonempty (
      H (triv (pairOf (inter_subset_left : baseP h U b ∩ baseO ψ a T ⊆ baseP h U b))) q ≃ₗ[ZMod 2]
        H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V U)
          a b T))) (q + k)))
    (hlow : ∀ q, q < k → ∀ z :
      H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V U)
        a b T))) q, z = 0)
    (hf : ∀ q, Module.Finite (ZMod 2) (lensH ψ U a b T q))
    (hz : ∀ q, A ≤ q → ∀ z : lensH ψ U a b T q, z = 0) :
    (∀ q, Module.Finite (ZMod 2)
      (H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V U)
        a b T))) q)) ∧
      ∀ q, q < k ∨ k + A ≤ q → ∀ z :
        H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V U)
          a b T))) q, z = 0 := by
  classical
  let e q := (baseLensEquiv ψ U a b T q).trans (Classical.choice (he q))
  constructor
  · intro q
    by_cases hq : q < k
    · exact Module.Finite.of_surjective
        (0 : ZMod 2 →ₗ[ZMod 2]
          H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V U)
            a b T))) q) (fun z => ⟨0, (hlow q hq z).symm⟩)
    · have hq' : q - k + k = q := by omega
      have := hf (q - k)
      rw [← hq']
      exact Module.Finite.equiv (e (q - k))
  · intro q hq
    rcases hq with hq | hq
    · exact hlow q hq
    · have hq' : q - k + k = q := by omega
      have hA : A ≤ q - k := by omega
      rw [← hq']
      intro z
      obtain ⟨y, rfl⟩ := (e (q - k)).surjective z
      rw [hz (q - k) hA y]
      exact (e (q - k)).map_zero

end

end Finsler.ProductShiftSupport

