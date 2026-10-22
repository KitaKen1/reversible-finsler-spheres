module

public import Finsler.Topology.SubspacePairs
public import Finsler.Topology.RootLensSupport
public import Finsler.Topology.RestrictedLensPairs

/-! Support for lenses of the actual descent restricted to a closed invariant subspace. -/

@[expose] public section

namespace Finsler.RestrictedRootSupport

open Set Finsler.FlowLens Finsler.LensFamily Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.LensContinuation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem support {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) (hc : Continuous g)
    {Z : Set W} (hZ : IsClosed Z)
    (hDZ : ∀ t (z : W), 0 ≤ t → z ∈ Z → D.flow t z ∈ Z)
    {a₀ b₀ c₀ : ℝ} (ha₀ : a₀ < c₀) (hb₀ : c₀ < b₀)
    (hK : IsCompact {w : W | a₀ ≤ g w ∧ g w ≤ b₀}) {U R : Set W} (hU : IsOpen U)
    (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ w ∈ Z, a₀ ≤ g w → g w ≤ b₀ → w ∉ U ∪ R → g (D.flow 1 w) < g w)
    (hval : ∀ w ∈ Z, a₀ ≤ g w → g w ≤ b₀ → g w ≠ c₀ → g (D.flow 1 w) < g w)
    (hab₀ : a₀ ≤ b₀) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_inter_left Z (sub_mono g hab₀)))) q))
    (hz : ∀ q, A ≤ q → ∀ x :
      H (triv (pairOf (inter_subset_inter_left Z (sub_mono g hab₀)))) q, x = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d →
      (∀ q, Module.Finite (ZMod 2)
        (lensH (Finsler.SubspaceK.subDescent D hDZ) (Subtype.val ⁻¹' U) a c t q)) ∧
        ∀ q, A ≤ q → ∀ x :
          lensH (Finsler.SubspaceK.subDescent D hDZ) (Subtype.val ⁻¹' U) a c t q, x = 0 := by
  obtain ⟨hfi, hzi⟩ := Finsler.SubspacePairs.support_inside Z (sub_mono g hab₀) A hf hz
  have hKi : IsCompact {w : TopCat.of Z | a₀ ≤ g w ∧ g w ≤ b₀} :=
    hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  apply Finsler.RootLensSupport.support (Finsler.SubspaceK.subDescent D hDZ)
    (hc.comp continuous_subtype_val) ha₀ hb₀ hKi (hU.preimage continuous_subtype_val)
    (hR.preimage continuous_subtype_val) (hUR.preimage _) _ _ hab₀ A hfi hzi
  · intro w ha hb hw
    change g (D.flow (max 1 0) w) < g w
    rw [max_eq_left zero_le_one]
    exact hout w w.2 ha hb hw
  · intro w ha hb hw
    change g (D.flow (max 1 0) w) < g w
    rw [max_eq_left zero_le_one]
    exact hval w w.2 ha hb hw

theorem ambient_support {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) (hc : Continuous g)
    {Z : Set W} (hZ : IsClosed Z)
    (hDZ : ∀ t (z : W), 0 ≤ t → z ∈ Z → D.flow t z ∈ Z)
    {a₀ b₀ c₀ : ℝ} (ha₀ : a₀ < c₀) (hb₀ : c₀ < b₀)
    (hK : IsCompact {w : W | a₀ ≤ g w ∧ g w ≤ b₀}) {U R : Set W} (hU : IsOpen U)
    (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ w ∈ Z, a₀ ≤ g w → g w ≤ b₀ → w ∉ U ∪ R → g (D.flow 1 w) < g w)
    (hval : ∀ w ∈ Z, a₀ ≤ g w → g w ≤ b₀ → g w ≠ c₀ → g (D.flow 1 w) < g w)
    (hab₀ : a₀ ≤ b₀) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_inter_left Z (sub_mono g hab₀)))) q))
    (hz : ∀ q, A ≤ q → ∀ x :
      H (triv (pairOf (inter_subset_inter_left Z (sub_mono g hab₀)))) q, x = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (inter_subset_inter_left Z (partY_sub_partU g D U a c t)))) q)) ∧
        ∀ q, A ≤ q → ∀ x :
          H (triv (pairOf (inter_subset_inter_left Z (partY_sub_partU g D U a c t)))) q, x = 0 := by
  obtain ⟨d, hd, hs⟩ := support D hc hZ hDZ ha₀ hb₀ hK hU hR hUR hout hval hab₀ A hf hz
  refine ⟨d, hd, fun a c t ht ha hc' hw => ?_⟩
  obtain ⟨hf', hz'⟩ := hs a c t ht ha hc' hw
  exact Finsler.RestrictedLensPairs.support_outside D hDZ U a c t (zero_le_one.trans ht) A hf' hz'

end

end Finsler.RestrictedRootSupport

