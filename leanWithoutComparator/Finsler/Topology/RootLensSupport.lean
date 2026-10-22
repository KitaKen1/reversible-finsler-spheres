module

public import Finsler.Topology.RootLens

/-! Finite support passes from a wide crossing to each lens of the same descent. -/

@[expose] public section

namespace Finsler.RootLensSupport

open Set Finsler.FlowLens Finsler.LensFamily Finsler.LevelCrossing Module

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem support {W : TopCat.{0}} {h : W → ℝ} (D : Descent W h) (hc : Continuous h)
    {a₀ b₀ c₀ : ℝ} (ha₀ : a₀ < c₀) (hb₀ : c₀ < b₀)
    (hK : IsCompact {w : W | a₀ ≤ h w ∧ h w ≤ b₀}) {Z R : Set W} (hZ : IsOpen Z)
    (hR : IsOpen R) (hZR : Disjoint Z R)
    (hout : ∀ w, a₀ ≤ h w → h w ≤ b₀ → w ∉ Z ∪ R → h (D.flow 1 w) < h w)
    (hval : ∀ w, a₀ ≤ h w → h w ≤ b₀ → h w ≠ c₀ → h (D.flow 1 w) < h w)
    (hab₀ : a₀ ≤ b₀) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH h hab₀ q))
    (hz : ∀ q, A ≤ q → ∀ x : crossH h hab₀ q, x = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d →
      (∀ q, Module.Finite (ZMod 2) (lensH D Z a c t q)) ∧
        ∀ q, A ≤ q → ∀ x : lensH D Z a c t q, x = 0 := by
  obtain ⟨d, hd, hl⟩ := Finsler.RootLens.lens_le_cross D hc ha₀ hb₀ hK hZ hR hZR
    hout hval hab₀
  refine ⟨d, hd, fun a c t ht ha hc' hw => ⟨fun q => (hl a c t ht ha hc' hw q (hf q)).1, ?_⟩⟩
  intro q hq x
  have := hf q
  have : Subsingleton (crossH h hab₀ q) :=
    ⟨fun u v => (hz q hq u).trans (hz q hq v).symm⟩
  have hzero : finrank (ZMod 2) (crossH h hab₀ q) = 0 :=
    Module.finrank_eq_zero_of_subsingleton _ _
  obtain ⟨hfinite, hrank⟩ := hl a c t ht ha hc' hw q (hf q)
  have := hfinite
  have hdim : finrank (ZMod 2) (lensH D Z a c t q) = 0 := by
    rw [hzero] at hrank
    exact Nat.eq_zero_of_le_zero hrank
  have : Subsingleton (lensH D Z a c t q) :=
    (Module.finrank_zero_iff (R := ZMod 2) (M := lensH D Z a c t q)).mp hdim
  exact Subsingleton.elim _ _

end

end Finsler.RootLensSupport

