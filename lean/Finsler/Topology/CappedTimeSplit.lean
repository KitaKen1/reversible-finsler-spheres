module

public import Finsler.Topology.TimeTriangleSplit

/-! An explicit output boundary compares the actual capped full time
interval with its two halves, in every output degree including zero. -/

@[expose] public section
namespace Finsler.CappedTimeSplit

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X Y Z : TopCat.{0}} (f : X ⊗ TopCat.I ⟶ Y) (d : ℕ)
  (u : ∀ q, (chains Y).X (d + q + 1) ⟶ (chains Z).X q)

def component (q : ℕ) : (chains X).X (d + q) ⟶ (chains Z).X q :=
  TimeTriangleSplit.interval X (d + q) ≫ (push f).f (d + q + 1) ≫ u q

def comparison (q : ℕ) : (chains X).X (d + q) ⟶ (chains Z).X (q + 1) :=
  TimeTriangleSplit.triangle X (d + q) ≫ (push f).f (d + q + 2) ≫ u (q + 1)

theorem cycle_boundary
    (hu : ∀ q, u (q + 1) ≫ (chains Z).d (q + 1) q =
      (chains Y).d (d + q + 2) (d + q + 1) ≫ u q) (q : ℕ) :
    ((chains X).iCycles (d + q) ≫ comparison f d u q) ≫ (chains Z).d (q + 1) q =
      (chains X).iCycles (d + q) ≫
        (component ((X ◁ IntervalTriangle.secondMap) ≫ f) d u q +
          component f d u q + component ((X ◁ IntervalTriangle.firstMap) ≫ f) d u q) := by
  have hf : (push f).f (d + q + 2) ≫ (chains Y).d (d + q + 2) (d + q + 1) =
      (chains (X ⊗ TopCat.I)).d (d + q + 2) (d + q + 1) ≫
        (push f).f (d + q + 1) := (push f).comm _ _
  calc
    _ = (((chains X).iCycles (d + q) ≫ TimeTriangleSplit.triangle X (d + q)) ≫
        (chains (X ⊗ TopCat.I)).d (d + q + 2) (d + q + 1)) ≫
          (push f).f (d + q + 1) ≫ u q := by
      simp only [comparison, Category.assoc, hu q]
      simpa only [Category.assoc] using congrArg
        (fun a => (chains X).iCycles (d + q) ≫ TimeTriangleSplit.triangle X (d + q) ≫ a ≫ u q) hf
    _ = _ := by
      rw [TimeTriangleSplit.cycle_boundary]
      simp only [component, push_comp, HomologicalComplex.comp_f, Category.assoc,
        Preadditive.add_comp, Preadditive.comp_add]

theorem full_split
    (hu : ∀ q, u (q + 1) ≫ (chains Z).d (q + 1) q =
      (chains Y).d (d + q + 2) (d + q + 1) ≫ u q) (q : ℕ) :
    (chains X).iCycles (d + q) ≫ component f d u q =
      (chains X).iCycles (d + q) ≫ component ((X ◁ IntervalTriangle.firstMap) ≫ f) d u q +
      (chains X).iCycles (d + q) ≫ component ((X ◁ IntervalTriangle.secondMap) ≫ f) d u q +
      ((chains X).iCycles (d + q) ≫ comparison f d u q) ≫ (chains Z).d (q + 1) q := by
  have hb := cycle_boundary f d u hu q
  simp only [Preadditive.comp_add] at hb
  let b := (chains X).iCycles (d + q) ≫ component ((X ◁ IntervalTriangle.firstMap) ≫ f) d u q
  let c := (chains X).iCycles (d + q) ≫ component ((X ◁ IntervalTriangle.secondMap) ≫ f) d u q
  have hbc : (b + c) + (b + c) = 0 := BorelCochain.two_eq_zero_of_mod (b + c)
  calc
    _ = ((chains X).iCycles (d + q) ≫ component f d u q) + ((b + c) + (b + c)) := by
      rw [hbc, add_zero]
    _ = (b + c) + (c + ((chains X).iCycles (d + q) ≫ component f d u q) + b) := by abel
    _ = _ := by rw [← hb]

end
end Finsler.CappedTimeSplit
