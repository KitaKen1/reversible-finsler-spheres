module

public import Finsler.Topology.LensConjugacy

/-! Conjugate actual lens pairs with corresponding fixed subsets. -/

@[expose] public section

namespace Finsler.FixedLensConjugacy

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation

noncomputable section
set_option autoImplicit false

variable {X Y : TopCat.{0}} {f : X → ℝ} {g : Y → ℝ}
  (D : Descent X f) (E : Descent Y g) (e : X ≃ₜ Y)
  (hfun : ∀ x, g (e x) = f x)
  (hflow : ∀ t x, E.flow t (e x) = e (D.flow t x))
  {U : Set X} {V : Set Y} (hUV : ∀ x, x ∈ U ↔ e x ∈ V)
  {Z : Set X} {W : Set Y} (hZW : ∀ x, x ∈ Z ↔ e x ∈ W)

include hfun hflow hUV hZW in
theorem nonempty_part_equiv (a b T : ℝ) (q : ℕ) :
    Nonempty (
      H (triv (pairOf (inter_subset_inter_left Z (partY_sub_partU f D U a b T)))) q ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_inter_left W (partY_sub_partU g E V a b T)))) q) := by
  have hU : ∀ x, x ∈ partU f U b ∩ Z ↔ e x ∈ partU g V b ∩ W := by
    intro x
    rw [mem_inter_iff, mem_inter_iff,
      Finsler.LensConjugacy.partU_iff e hfun hUV, hZW]
  have hY : ∀ x, x ∈ partY f D U a b T ∩ Z ↔ e x ∈ partY g E V a b T ∩ W := by
    intro x
    rw [mem_inter_iff, mem_inter_iff,
      Finsler.LensConjugacy.partY_iff D E e hfun hflow hUV, hZW]
  have hb := bijective_Hmap_of_homeomorph
    (inter_subset_inter_left Z (partY_sub_partU f D U a b T))
    (inter_subset_inter_left W (partY_sub_partU g E V a b T)) e hU hY q
  exact ⟨(LinearEquiv.ofBijective _ hb).symm⟩

end

end Finsler.FixedLensConjugacy

