module

public import Finsler.Loop.ShuffleWords
public import Finsler.Topology.ShuffleBlockNormalization
import all TauCeti.AlgebraicTopology.SimplicialSet.Shuffle

/-! Concrete standard product simplices for arbitrary shuffle words.
Coordinates are prefix counts, clamped to the target simplex. Clamping
makes every word well typed and commutes with the actual cone steps. -/

@[expose] public section
namespace Finsler.ShuffleWordSimplex

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ShuffleWords
open scoped Simplicial DoldKan BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

def simplex (p q N : ℕ) (w : List Bool) : ((Δ[p] : SSet.{0}) ⊗ Δ[q]) _⦋N⦌ :=
  (SSet.stdSimplex.objMk (n := ⦋p⦌) (m := Opposite.op ⦋N⦌)
    (show Fin (N + 1) →o Fin (p + 1) from
    { toFun := fun i => ⟨min (horizontal (w.take i.val)) p, Nat.lt_succ_of_le (min_le_right _ _)⟩
      monotone' := by
        intro i j hij
        change min (horizontal (w.take i.val)) p ≤ min (horizontal (w.take j.val)) p
        exact min_le_min (horizontal_take_mono w hij) le_rfl }),
   SSet.stdSimplex.objMk (n := ⦋q⦌) (m := Opposite.op ⦋N⦌)
    (show Fin (N + 1) →o Fin (q + 1) from
    { toFun := fun i => ⟨min (vertical (w.take i.val)) q, Nat.lt_succ_of_le (min_le_right _ _)⟩
      monotone' := by
        intro i j hij
        change min (vertical (w.take i.val)) q ≤ min (vertical (w.take j.val)) q
        exact min_le_min (vertical_take_mono w hij) le_rfl }))

theorem horizontal_step (p q N : ℕ) (w : List Bool) :
    simplex (p + 1) q (N + 1) (false :: w) =
      SSet.stdSimplex.prodCone ((SSet.stdSimplex.δ 0 ▷ (Δ[q] : SSet.{0})).app
        (Opposite.op ⦋N⦌) (simplex p q N w)) := by
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      apply Fin.ext
      change min (horizontal ((false :: w).take (i.val + 1))) (p + 1) =
        min (horizontal (w.take i.val)) p + 1
      simp only [List.take_succ_cons, horizontal]
      omega
  · apply SSet.stdSimplex.ext
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl

theorem vertical_step (p q N : ℕ) (w : List Bool) :
    simplex p (q + 1) (N + 1) (true :: w) =
      SSet.stdSimplex.prodCone (((Δ[p] : SSet.{0}) ◁ SSet.stdSimplex.δ 0).app
        (Opposite.op ⦋N⦌) (simplex p q N w)) := by
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  · apply SSet.stdSimplex.ext
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      apply Fin.ext
      change min (vertical ((true :: w).take (i.val + 1))) (q + 1) =
        min (vertical (w.take i.val)) q + 1
      simp only [List.take_succ_cons, vertical]
      omega

theorem prefix_horizontal_count (a i : ℕ) (w : List Bool) :
    horizontal ((List.replicate a false ++ w).take (a + i)) = a + horizontal (w.take i) := by
  induction a with
  | zero => simp [horizontal]
  | succ a ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.succ_add, List.take_succ_cons, horizontal]
    rw [ih]

theorem prefix_vertical_count (a i : ℕ) (w : List Bool) :
    vertical ((List.replicate a false ++ w).take (a + i)) = vertical (w.take i) := by
  induction a with
  | zero => simp
  | succ a ih =>
    simpa only [List.replicate_succ, List.cons_append, Nat.succ_add, List.take_succ_cons,
      vertical] using ih

theorem prefix_front_horizontal (a i : ℕ) (hi : i ≤ a) (w : List Bool) :
    horizontal ((List.replicate a false ++ w).take i) = i := by
  induction a generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    rfl
  | succ a ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [List.replicate_succ, List.cons_append, List.take_succ_cons, horizontal] using
        congrArg (fun n => n + 1) (ih i (by omega))

theorem prefix_front_vertical (a i : ℕ) (hi : i ≤ a) (w : List Bool) :
    vertical ((List.replicate a false ++ w).take i) = 0 := by
  induction a generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    rfl
  | succ a ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [List.replicate_succ, List.cons_append, List.take_succ_cons, vertical] using
        ih i (by omega)

theorem horizontal_front (a p N : ℕ) (ha : a ≤ N) (w : List Bool) :
    (Δ[a + p] : SSet.{0}).map (SimplexCategory.subinterval 0 a (by omega)).op
      (simplex (a + p) 0 N (List.replicate a false ++ w)).1 =
        SSet.stdSimplex.objEquiv.symm (SimplexCategory.subinterval 0 a (by omega)) := by
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  change min (horizontal ((List.replicate a false ++ w).take (i.val + 0))) (a + p) = i.val + 0
  rw [Nat.add_zero, prefix_front_horizontal a i.val (by omega)]
  omega

theorem horizontal_tail (a p q N : ℕ) (w : List Bool) :
    ((Δ[a + p] : SSet.{0}) ⊗ Δ[q]).map (SimplexCategory.subinterval a N (by omega)).op
      (simplex (a + p) q (a + N) (List.replicate a false ++ w)) =
    (SSet.stdSimplex.map (SimplexCategory.subinterval a p (by omega)) ▷ (Δ[q] : SSet.{0})).app
      (Opposite.op ⦋N⦌) (simplex p q N w) := by
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro i
    apply Fin.ext
    change min (horizontal ((List.replicate a false ++ w).take (i.val + a))) (a + p) =
      min (horizontal (w.take i.val)) p + a
    rw [Nat.add_comm i.val a, prefix_horizontal_count]
    omega
  · apply SSet.stdSimplex.ext
    intro i
    apply Fin.ext
    change min (vertical ((List.replicate a false ++ w).take (i.val + a))) q =
      min (vertical (w.take i.val)) q
    rw [Nat.add_comm i.val a, prefix_vertical_count]

end
end Finsler.ShuffleWordSimplex
