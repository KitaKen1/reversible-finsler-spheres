module

public import Finsler.Topology.ProductShiftSupport
public import Finsler.Topology.RootLensSupport

/-! A root crossing support cutoff gives a finite shifted support interval for the
actual product flow. Compact-band trapping and the strip condition come from the
same root descent. The negative dimension is independent of the root support cutoff. -/

@[expose] public section

namespace Finsler.ProductRootSupport

open Set Finsler.FlowLens Finsler.LensFamily Finsler.LensTrap
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.ConeLens Finsler.ProductModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_support {B : TopCat.{0}} {h : B → ℝ} (ψ : Descent B h) (hh : Continuous h)
    (k : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a₀ b₀ c₀ : ℝ} (ha₀ : a₀ < c₀) (hb₀ : c₀ < b₀)
    (hK : IsCompact {z : B | a₀ ≤ h z ∧ h z ≤ b₀}) {U R : Set B}
    (hU : IsOpen U) (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ z, a₀ ≤ h z → h z ≤ b₀ → z ∉ U ∪ R → h (ψ.flow 1 z) < h z)
    (hval : ∀ z, a₀ ≤ h z → h z ≤ b₀ → h z ≠ c₀ → h (ψ.flow 1 z) < h z)
    (hab₀ : a₀ ≤ b₀) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH h hab₀ q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH h hab₀ q, z = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, 1 ≤ T → a < c₀ → c₀ < b →
      a₀ ≤ a - (b - a) / (Real.exp (2 * T) - 1) →
      b + (b - a) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (b + (b - a) / (Real.exp (2 * T) - 1)) - (a - (b - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V U)
          a b T))) q)) ∧
        ∀ q, q < k ∨ k + A ≤ q → ∀ z :
          H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh) (over k V U)
            a b T))) q, z = 0 := by
  obtain ⟨dr, hdr, hr⟩ := Finsler.RootLensSupport.support ψ hh ha₀ hb₀ hK hU hR hUR
    hout hval hab₀ A hf hz
  obtain ⟨dp, hdp, hp⟩ := Finsler.ProductShiftSupport.exists_equiv ψ k V hh hU hR hUR hK hout
  refine ⟨min dr dp, lt_min hdr hdp, fun a b T hT ha hb hlo hhi hw => ?_⟩
  have hab : a ≤ b := (ha.trans hb).le
  have hε := Finsler.ProductShift.eps_nonneg hab hT
  have hwr : b - a < dr := by
    have h := hw.trans_le (min_le_left dr dp)
    linarith
  have hwp := hw.trans_le (min_le_right dr dp)
  have hstrip : ∀ z, b ≤ h z → h z ≤ b + (b - a) / (Real.exp (2 * T) - 1) →
      h (ψ.flow 1 z) < h z := by
    intro z hzb hzu
    exact hval z (by linarith) (hzu.trans hhi) (by linarith)
  obtain ⟨he, hlow⟩ := hp a b T hT hab hlo hhi hwp hstrip
  obtain ⟨hfr, hzr⟩ := hr a b T hT ha hb hwr
  exact Finsler.ProductShiftSupport.support_of_shift ψ k V hh U a b T A he hlow hfr hzr

end

end Finsler.ProductRootSupport
