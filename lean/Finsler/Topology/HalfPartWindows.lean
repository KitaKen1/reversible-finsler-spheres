module

public import Finsler.Topology.HalfLens
public import Finsler.Topology.SwapWindows
public import Finsler.Topology.SmallLevel

/-! Ordinary windows of one open half supply reflection-Borel windows of its orbit part,
also inside an invariant fixed set. This applies to the actual ambient packet descent. -/

@[expose] public section

namespace Finsler.HalfPartWindows

open CategoryTheory Set Finsler.InvPairs Finsler.PolySplit Finsler.FlowLens
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelComparison Finsler.LensFamily Finsler.LensContinuation

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem H_pair_eq_zero {X : TopCat.{0}} {s t : Set X} (hst : s ⊆ t) (hts : t ⊆ s)
    (q : ℕ) (x : H (triv (pairOf hst)) q) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_zero_iff_coboundary]
  have hc : (c : (triv (pairOf hst)).C q) = 0 :=
    Finsler.SmallLevel.relative_eq_zero hst hts q c.1
  rw [hc]
  exact Submodule.zero_mem _

theorem fixed_lens_eq_zero {X : TopCat.{0}} {g : X → ℝ} (D : Descent X g)
    {U Z : Set X} (hdis : Disjoint U Z) (a b T : ℝ) (q : ℕ)
    (x : H (triv (pairOf (inter_subset_inter_left Z (partY_sub_partU g D U a b T)))) q) :
    x = 0 := by
  apply H_pair_eq_zero _ ?_ q x
  intro y hy
  exact False.elim (Set.disjoint_left.mp hdis hy.1.2 hy.2)

theorem orbit_swap {X : TopCat.{0}} (k : KAct X) {U : Set X}
    (hdis : Disjoint U (k.ρ ⁻¹' U)) (x : X) (hx : x ∈ U ∪ k.ρ ⁻¹' U) :
    k.ρ x ∈ U ↔ x ∉ U := by
  constructor
  · intro h hxU
    exact Set.disjoint_left.mp hdis hxU h
  · intro h
    rcases hx with hx | hx
    · exact False.elim (h hx)
    · exact hx

variable {X : TopCat.{0}} (k : KAct X) {g : X → ℝ}
  (hgρ : ∀ x, g (k.ρ x) = g x) (hgσ : ∀ x, g (k.σ x) = g x)
  (D : Descent X g)
  (hDρ : ∀ t x, D.flow t (k.ρ x) = k.ρ (D.flow t x))
  (hDσ : ∀ t x, D.flow t (k.σ x) = k.σ (D.flow t x))
  {a' a b T : ℝ} (ha : a' < a) {J : Type}
  (𝒲 : J → Set X) (h𝒲K : ∀ j, Inv k (𝒲 j)) (j : J)
  {U : Set X} (hU : IsOpen U) (hdis : Disjoint U (k.ρ ⁻¹' U))
  (h𝒲 : 𝒲 j = U ∪ k.ρ ⁻¹' U)

include ha hU hdis h𝒲

theorem part_eq_zero (hg : Continuous g) {q : ℕ}
    (hz : ∀ x : lensH D U a b T q, x = 0)
    (x : HR (partComplex k hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j) q) : x = 0 := by
  have hzero : ∀ y : lensH D (𝒲 j) a b T q, y = 0 := by
    rw [h𝒲]
    exact Finsler.HalfLens.lens_half_eq_zero D k hgρ hDρ hU hdis hz
  apply Finsler.SwapWindows.HR_gComplex_eq_zero k _ _ _ hU ?_ ?_ x
  · intro y hy
    exact orbit_swap k hdis y (h𝒲 ▸ hy.2)
  · exact Finsler.HalfLens.part_eq_zero D hg ha (𝒲 j) hzero

theorem fixed_part_eq_zero {Z : Set X} (hZ : Inv k Z) (hg : Continuous g) {q : ℕ}
    (hz : ∀ x : H (triv (pairOf (Finsler.HalfLens.fixLens_sub D U Z a b T))) q, x = 0)
    (x : HR (fixPartComplex k hZ hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j) q) : x = 0 := by
  have hzero : ∀ y : H (triv (pairOf
      (Finsler.HalfLens.fixLens_sub D (𝒲 j) Z a b T))) q, y = 0 := by
    rw [h𝒲]
    exact Finsler.HalfLens.fixLens_half_eq_zero D k hgρ hDρ hZ.ρ_mem hU hdis hz
  apply Finsler.SwapWindows.HR_gComplex_eq_zero k _ _ _ hU ?_ ?_ x
  · intro y hy
    exact orbit_swap k hdis y (h𝒲 ▸ hy.2)
  · exact Finsler.HalfLens.fixPart_eq_zero D hg ha (𝒲 j) Z hzero

end

end Finsler.HalfPartWindows
