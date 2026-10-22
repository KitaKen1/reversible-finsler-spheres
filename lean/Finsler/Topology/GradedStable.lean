module

public import Finsler.Topology.GradedLadder

/-! Vanishing of the potential of graded families. If all pieces and the space of the upper
degree vanish, the potential is zero. If the pieces vanish above the cutoff, the total comparison
map of the upper degree is bijective and that of the lower degree is surjective, the potential is
zero: nothing is missing from the truncated images and no class is invisible. -/

@[expose] public section

namespace Finsler.GradedStable

open Module
open Finsler.TripleK Finsler.TotalExact Finsler.LadderBudget Finsler.GradedLadder

noncomputable section

variable (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
  {Y X : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup X] [Module (ZMod 2) X]

/-- If all pieces and the space of the upper degree vanish, the potential is zero. -/
theorem gphi_eq_zero_of_vanish (hG : ∀ q (x : G q), x = 0) (hY : ∀ y : Y, y = 0) (j : ℕ)
    (eY : ∀ l, Y →ₗ[ZMod 2] G l) (eX : ∀ l, X →ₗ[ZMod 2] G l) : gphi G j eY eX = 0 := by
  have hsub : Subsingleton ((q : ℕ) → G q) :=
    ⟨fun x y => funext fun q => (hG q (x q)).trans (hG q (y q)).symm⟩
  have hsubY : Subsingleton Y := ⟨fun y y' => (hY y).trans (hY y').symm⟩
  have h1 : finrank (ZMod 2) (LinearMap.range (cut G j)) = 0 := finrank_zero_of_subsingleton
  have h2 : finrank (ZMod 2) ((LinearMap.range (totMap eY)).map (cut G j)) = 0 :=
    finrank_zero_of_subsingleton
  have h3 : finrank (ZMod 2) ((LinearMap.range (totMap eX)).map (cut G j)) = 0 :=
    finrank_zero_of_subsingleton
  have h4 : finrank (ZMod 2) Y = 0 := finrank_zero_of_subsingleton
  unfold gphi potential
  rw [h1, h2, h3, h4]
  rfl

/-- If the pieces vanish above the cutoff, the total comparison map of the upper degree is
bijective and that of the lower degree is surjective, the potential is zero. -/
theorem gphi_eq_zero_of_stable (j : ℕ) (hj : ∀ l, j < l → ∀ x : G l, x = 0)
    (eY : ∀ l, Y →ₗ[ZMod 2] G l) (eX : ∀ l, X →ₗ[ZMod 2] G l)
    (hY : Function.Bijective (totMap eY)) (hX : Function.Surjective (totMap eX)) :
    gphi G j eY eX = 0 := by
  have hcut : LinearMap.range (cut G j) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (mem_range_cut j x).mpr fun q hq => hj q hq (x q)
  have hrY : LinearMap.range (totMap eY) = ⊤ := LinearMap.range_eq_top.mpr hY.2
  have hrX : LinearMap.range (totMap eX) = ⊤ := LinearMap.range_eq_top.mpr hX
  have h2 : (LinearMap.range (totMap eY)).map (cut G j) = ⊤ := by
    rw [hrY, Submodule.map_top, hcut]
  have h3 : (LinearMap.range (totMap eX)).map (cut G j) = ⊤ := by
    rw [hrX, Submodule.map_top, hcut]
  have h4 : finrank (ZMod 2) Y = finrank (ZMod 2) ((q : ℕ) → G q) :=
    (LinearEquiv.ofBijective (totMap eY) hY).finrank_eq
  unfold gphi potential
  rw [hcut, h2, h3, h4, finrank_top]
  ring

end

end Finsler.GradedStable
