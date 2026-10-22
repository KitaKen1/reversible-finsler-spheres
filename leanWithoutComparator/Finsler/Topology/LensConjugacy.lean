module

public import Finsler.Topology.LensContinuation

/-! transport actual lens pairs under a conjugacy of flows.
This does not identify lens pairs of arbitrary unrelated descents.  -/

@[expose] public section

namespace Finsler.LensConjugacy

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation
noncomputable section

variable {X Y : TopCat.{0}} {f : X → ℝ} {g : Y → ℝ}
  (D : Descent X f) (E : Descent Y g) (e : X ≃ₜ Y)
  (hfun : ∀ x, g (e x) = f x)
  (hflow : ∀ t x, E.flow t (e x) = e (D.flow t x))
  {U : Set X} {V : Set Y} (hUV : ∀ x, x ∈ U ↔ e x ∈ V)

include hfun hUV

theorem partU_iff (b : ℝ) (x : X) : x ∈ partU f U b ↔ e x ∈ partU g V b := by
  change (f x < b ∧ x ∈ U) ↔ (g (e x) < b ∧ e x ∈ V)
  rw [hfun, hUV]

include hflow

theorem partY_iff (a b T : ℝ) (x : X) :
    x ∈ partY f D U a b T ↔ e x ∈ partY g E V a b T := by
  change (f x < b ∧ f (D.flow T x) < a ∧ x ∈ U) ↔
    (g (e x) < b ∧ g (E.flow T (e x)) < a ∧ e x ∈ V)
  rw [hflow, hfun, hfun, hUV]

def pairHom (a b T : ℝ) : pairOf (partY_sub_partU f D U a b T) ⟶
    pairOf (partY_sub_partU g E V a b T) :=
  pairMapX (partY_sub_partU f D U a b T) (partY_sub_partU g E V a b T)
    (restrictMap e fun x hx => (partU_iff e hfun hUV b x).mp hx)
    (fun x hx => (partY_iff D E e hfun hflow hUV a b T x).mp hx)

theorem pair_bijective (a b T : ℝ) (q : ℕ) :
    Function.Bijective (Hmap (trivHom (pairHom D E e hfun hflow hUV a b T)) q) :=
  bijective_Hmap_of_homeomorph (partY_sub_partU f D U a b T)
    (partY_sub_partU g E V a b T) e (partU_iff e hfun hUV b)
    (partY_iff D E e hfun hflow hUV a b T) q

theorem nonempty_part_equiv (a b T : ℝ) (q : ℕ) :
    Nonempty (H (triv (pairOf (partY_sub_partU f D U a b T))) q ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU g E V a b T))) q) :=
  ⟨(LinearEquiv.ofBijective _ (pair_bijective D E e hfun hflow hUV a b T q)).symm⟩

theorem finrank_eq (a b T : ℝ) (q : ℕ) :
    Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU f D U a b T))) q) =
      Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU g E V a b T))) q) := by
  obtain ⟨equiv⟩ := nonempty_part_equiv D E e hfun hflow hUV a b T q
  exact equiv.finrank_eq

theorem vanish_iff (a b T : ℝ) (q : ℕ) :
    (∀ x : H (triv (pairOf (partY_sub_partU f D U a b T))) q, x = 0) ↔
      (∀ y : H (triv (pairOf (partY_sub_partU g E V a b T))) q, y = 0) := by
  obtain ⟨equiv⟩ := nonempty_part_equiv D E e hfun hflow hUV a b T q
  constructor
  · intro h y
    have he := congrArg equiv (h (equiv.symm y))
    simpa only [equiv.apply_symm_apply, map_zero] using he
  · intro h x
    exact equiv.injective ((h (equiv x)).trans (map_zero equiv).symm)

end

end Finsler.LensConjugacy
