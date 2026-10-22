module

public import Finsler.Topology.ProductRootSupport

/-! Positive scaling of root energy keeps the actual flow and the cohomology cutoff. -/

@[expose] public section

namespace Finsler.ScaledRootSupport

open Set Finsler.FlowLens Finsler.LensFamily Finsler.ConeLens Finsler.ProductModel
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {B : TopCat.{0}} {h : B → ℝ}

def scaleDescent (ψ : Descent B h) (r : ℝ) (hr : 0 ≤ r) : Descent B (fun z => r * h z) where
  flow := ψ.flow
  cont := ψ.cont
  zero := ψ.zero
  add := ψ.add
  mono t z ht := mul_le_mul_of_nonneg_left (ψ.mono t z ht) hr

theorem sub_scale (r : ℝ) (hr : 0 < r) (a : ℝ) :
    sub (fun z => r * h z) (r * a) = sub h a := by
  ext z
  exact mul_lt_mul_iff_right₀ hr

theorem band_scale (r : ℝ) (hr : 0 < r) (a b : ℝ) :
    {z : B | r * a ≤ r * h z ∧ r * h z ≤ r * b} = {z : B | a ≤ h z ∧ h z ≤ b} := by
  ext z
  simp only [mem_ofPred_eq, mul_le_mul_iff_right₀ hr]

def crossEquiv (r : ℝ) (hr : 0 < r) {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    crossH (fun z => r * h z) (mul_le_mul_of_nonneg_left hab hr.le) q ≃ₗ[ZMod 2]
      crossH h hab q :=
  Finsler.SubspacePairs.equalHEquiv (sub_scale r hr a) (sub_scale r hr b) _ _ q

theorem cross_support (r : ℝ) (hr : 0 < r) {a b : ℝ} (hab : a ≤ b) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH h hab q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH h hab q, z = 0) :
    (∀ q, Module.Finite (ZMod 2)
      (crossH (fun z => r * h z) (mul_le_mul_of_nonneg_left hab hr.le) q)) ∧
      ∀ q, A ≤ q → ∀ z :
        crossH (fun z => r * h z) (mul_le_mul_of_nonneg_left hab hr.le) q, z = 0 := by
  constructor
  · intro q
    have := hf q
    exact Module.Finite.equiv (crossEquiv r hr hab q).symm
  · intro q hq z
    exact (crossEquiv r hr hab q).injective
      ((hz q hq ((crossEquiv r hr hab q) z)).trans (crossEquiv r hr hab q).map_zero.symm)

theorem product_support (ψ : Descent B h) (hh : Continuous h) (r : ℝ) (hr : 0 < r)
    (k : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a₀ b₀ c₀ : ℝ} (ha₀ : a₀ < c₀) (hb₀ : c₀ < b₀)
    (hK : IsCompact {z : B | a₀ ≤ h z ∧ h z ≤ b₀}) {U R : Set B}
    (hU : IsOpen U) (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ z, a₀ ≤ h z → h z ≤ b₀ → z ∉ U ∪ R → h (ψ.flow 1 z) < h z)
    (hval : ∀ z, a₀ ≤ h z → h z ≤ b₀ → h z ≠ c₀ → h (ψ.flow 1 z) < h z)
    (hab₀ : a₀ ≤ b₀) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH h hab₀ q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH h hab₀ q, z = 0) :
    let hh' : Continuous (fun z => r * h z) := continuous_const.mul hh
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, 1 ≤ T → a < r * c₀ → r * c₀ < b →
      r * a₀ ≤ a - (b - a) / (Real.exp (2 * T) - 1) →
      b + (b - a) / (Real.exp (2 * T) - 1) ≤ r * b₀ →
      (b + (b - a) / (Real.exp (2 * T) - 1)) - (a - (b - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (setY_sub_setU (cone k V hh') (descent k V (scaleDescent ψ r hr.le) hh')
          (over k V U) a b T))) q)) ∧
        ∀ q, q < k ∨ k + A ≤ q → ∀ z :
          H (triv (pairOf (setY_sub_setU (cone k V hh') (descent k V (scaleDescent ψ r hr.le) hh')
            (over k V U) a b T))) q, z = 0 := by
  dsimp only
  obtain ⟨hfs, hzs⟩ := cross_support r hr hab₀ A hf hz
  have hKs : IsCompact {z : B | r * a₀ ≤ r * h z ∧ r * h z ≤ r * b₀} := by
    rw [band_scale r hr a₀ b₀]
    exact hK
  apply Finsler.ProductRootSupport.exists_support (scaleDescent ψ r hr.le)
    (continuous_const.mul hh) k V (mul_lt_mul_of_pos_left ha₀ hr)
    (mul_lt_mul_of_pos_left hb₀ hr) hKs hU hR hUR _ _
    (mul_le_mul_of_nonneg_left hab₀ hr.le) A hfs hzs
  · intro z ha hb hz
    exact mul_lt_mul_of_pos_left
      (hout z (le_of_mul_le_mul_left ha hr) (le_of_mul_le_mul_left hb hr) hz) hr
  · intro z ha hb hz
    apply mul_lt_mul_of_pos_left _ hr
    apply hval z (le_of_mul_le_mul_left ha hr) (le_of_mul_le_mul_left hb hr)
    intro he
    exact hz (congrArg (fun x => r * x) he)

end

end Finsler.ScaledRootSupport

