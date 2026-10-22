module

public import Finsler.Topology.FilteredRightUnit

/-! Constant-loop classes and both filtered unit formulas in the existing absolute loop model.
This does not identify D_T S with the constant-loop class or define a global product. -/

@[expose] public section

namespace Finsler.AbsoluteFilteredUnits

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.CochainComparison Finsler.SphereUnitCandidate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def cutMap {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    TopCat.of (lev F a) ⟶ TopCat.of (lev F b) := TopPair.Hom.fst (cutPair F hab)

def forget {n : ℕ} (F : ReversibleMetric n) (a : ℝ) :
    TopCat.of (lev F a) ⟶ (fullPair n).fst := TopPair.Hom.fst (resPair F a)

def constant (n : ℕ) : sphere n ⟶ (fullPair n).fst :=
  TopCat.ofHom ⟨fun x => ⟨IntervalSobolev.constantSphereLoop x, Set.mem_univ _⟩,
    (SphereTopClass.constantSphereLoop_continuous n).subtype_mk _⟩

def absoluteCandidate (n : ℕ) (hn : 1 ≤ n) : PoolCap.homology (fullPair n).fst n :=
  (PoolCap.push (constant n) n).hom (fundamental n hn)

theorem constant_cut {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    constantMap F a ≫ cutMap F hab = constantMap F b := by ext x : 1; rfl

theorem constant_forget {n : ℕ} (F : ReversibleMetric n) (a : ℝ) :
    constantMap F a ≫ forget F a = constant n := by ext x : 1; rfl

theorem constant_evaluation (n : ℕ) : constant n ≫ fullEval n = 𝟙 (sphere n) := by
  ext x : 1
  exact eval_constant x

theorem candidate_cut {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    (PoolCap.push (cutMap F hab) n).hom (candidate hn F a) = candidate hn F b := by
  let H := (singularHomologyFunctor (ModuleCat (ZMod 2)) n).obj coeff
  have he := ConcreteCategory.congr_hom (H.map_comp (constantMap F a) (cutMap F hab)) (fundamental n hn)
  rw [constant_cut] at he
  exact he.symm

theorem candidate_forget {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (a : ℝ) :
    (PoolCap.push (forget F a) n).hom (candidate hn F a) = absoluteCandidate n hn := by
  let H := (singularHomologyFunctor (ModuleCat (ZMod 2)) n).obj coeff
  have he := ConcreteCategory.congr_hom (H.map_comp (constantMap F a) (forget F a)) (fundamental n hn)
  rw [constant_forget] at he
  exact he.symm

theorem absolute_evaluation (n : ℕ) (hn : 1 ≤ n) :
    (PoolCap.push (fullEval n) n).hom (absoluteCandidate n hn) = fundamental n hn := by
  let H := (singularHomologyFunctor (ModuleCat (ZMod 2)) n).obj coeff
  have he := ConcreteCategory.congr_hom (H.map_comp (constant n) (fullEval n)) (fundamental n hn)
  rw [constant_evaluation, CategoryTheory.Functor.map_id] at he
  exact he.symm

theorem absoluteCandidate_ne_zero (n : ℕ) (hn : 1 ≤ n) : absoluteCandidate n hn ≠ 0 := by
  intro hz
  have he := absolute_evaluation n hn
  rw [hz, map_zero] at he
  exact fundamental_ne_zero n hn he.symm

theorem left_inclusion_forget {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    FilteredLeftUnit.inclusion F hp hq hε ≫ forget F (p + (q + ε)) = forget F q := by ext x : 1; rfl

theorem right_inclusion_forget {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    FilteredRightUnit.inclusion F hp hq hε ≫ forget F (p + (q + ε)) = forget F p := by ext x : 1; rfl

theorem left_unit_absolute {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ)
    (y : PoolCap.homology (TopCat.of (lev F q)) k) :
    (PoolCap.push (forget F (p + (q + ε))) k).hom
      (FilteredBilinearLoopProduct.product hn F hp hq hε n k k rfl (candidate hn F p) y) =
        (PoolCap.push (forget F q) k).hom y := by
  rw [FilteredLeftUnit.left_unit]
  have he := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff).map_comp
      (FilteredLeftUnit.inclusion F hp hq hε) (forget F (p + (q + ε)))) y
  rw [left_inclusion_forget] at he
  exact he.symm

theorem right_unit_absolute {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ)
    (x : PoolCap.homology (TopCat.of (lev F p)) k) :
    (PoolCap.push (forget F (p + (q + ε))) k).hom
      (FilteredBilinearLoopProduct.product hn F hp hq hε k n k (Nat.add_comm k n) x (candidate hn F q)) =
        (PoolCap.push (forget F p) k).hom x := by
  rw [FilteredRightUnit.right_unit]
  have he := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff).map_comp
      (FilteredRightUnit.inclusion F hp hq hε) (forget F (p + (q + ε)))) x
  rw [right_inclusion_forget] at he
  exact he.symm

end
end Finsler.AbsoluteFilteredUnits
