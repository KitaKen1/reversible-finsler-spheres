module

public import Finsler.Topology.TimeTriangleSplit
public import Finsler.Topology.TimePrismNaturality

/-! Split the ACTUAL singular time prism before any cap operation.
The genuine interval triangle supplies an explicit output boundary
for two halves and four quarters, in every source degree. -/

@[expose] public section
namespace Finsler.UncappedTimeSplit
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {X Y : TopCat.{0}} (f : X ⊗ TopCat.I ⟶ Y)

def first : X ⊗ TopCat.I ⟶ Y := (X ◁ IntervalTriangle.firstMap) ≫ f
def second : X ⊗ TopCat.I ⟶ Y := (X ◁ IntervalTriangle.secondMap) ≫ f

def component (j : ℕ) : (chains X).X j ⟶ (chains Y).X (j + 1) :=
  TimeTriangleSplit.interval X j ≫ (push f).f (j + 1)

def comparison (j : ℕ) : (chains X).X j ⟶ (chains Y).X (j + 2) :=
  TimeTriangleSplit.triangle X j ≫ (push f).f (j + 2)

theorem cycle_boundary (j : ℕ) :
    ((chains X).iCycles j ≫ comparison f j) ≫ (chains Y).d (j + 2) (j + 1) =
      (chains X).iCycles j ≫ (component (second f) j + component f j + component (first f) j) := by
  calc
    _ = (((chains X).iCycles j ≫ TimeTriangleSplit.triangle X j) ≫
        (chains (X ⊗ TopCat.I)).d (j + 2) (j + 1)) ≫ (push f).f (j + 1) := by
      simp only [comparison, Category.assoc, (push f).comm]
    _ = _ := by
      rw [TimeTriangleSplit.cycle_boundary]
      simp only [component, first, second, push_comp, HomologicalComplex.comp_f,
        Category.assoc, Preadditive.add_comp, Preadditive.comp_add]

theorem full_split (j : ℕ) : (chains X).iCycles j ≫ component f j =
    (chains X).iCycles j ≫ component (first f) j +
    (chains X).iCycles j ≫ component (second f) j +
    ((chains X).iCycles j ≫ comparison f j) ≫ (chains Y).d (j + 2) (j + 1) := by
  have h := cycle_boundary f j
  simp only [Preadditive.comp_add] at h
  let a := (chains X).iCycles j ≫ component (first f) j
  let b := (chains X).iCycles j ≫ component (second f) j
  have hz : (a + b) + (a + b) = 0 := BorelCochain.two_eq_zero_of_mod _
  calc
    _ = ((chains X).iCycles j ≫ component f j) + ((a + b) + (a + b)) := by rw [hz, add_zero]
    _ = (a + b) + (b + ((chains X).iCycles j ≫ component f j) + a) := by abel
    _ = _ := by rw [← h]

def fourComparison (j : ℕ) : (chains X).X j ⟶ (chains Y).X (j + 2) :=
  comparison f j + comparison (first f) j + comparison (second f) j

theorem four_split (j : ℕ) : (chains X).iCycles j ≫ component f j =
    (chains X).iCycles j ≫ component (first (first f)) j +
    (chains X).iCycles j ≫ component (second (first f)) j +
    (chains X).iCycles j ≫ component (first (second f)) j +
    (chains X).iCycles j ≫ component (second (second f)) j +
    ((chains X).iCycles j ≫ fourComparison f j) ≫ (chains Y).d (j + 2) (j + 1) := by
  calc
    _ = ((chains X).iCycles j ≫ component (first f) j) +
        ((chains X).iCycles j ≫ component (second f) j) +
        ((chains X).iCycles j ≫ comparison f j) ≫ (chains Y).d (j + 2) (j + 1) := full_split f j
    _ = _ := by
      rw [full_split (first f) j, full_split (second f) j]
      simp only [fourComparison, Preadditive.comp_add, Preadditive.add_comp]
      abel

theorem prism_component {g h : X ⟶ Y} (H : TopCat.Homotopy g h) (j : ℕ) :
    component H.h j = (H.toSSet.chainComplexMap coeff).hom j (j + 1) :=
  TimeShuffleComparison.rectangle_eq_prism H j

end
end Finsler.UncappedTimeSplit
