module

public import Finsler.Loop.RightIntervalCochain
public import Finsler.Topology.SingularTimeModelComparison
public import Finsler.Loop.NativeIntervalGHTests
public import Finsler.Loop.NativeRawTimeSquareBoundary

/-! Actual coordinate maps for the two original time insertions and
the singular product-time model. The raw clocks and the original
SelfCutTimePrism are retained, before any scalar comparison. -/
@[expose] public section
namespace Finsler.TwoTimeSquareCoordinates
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.IntervalSobolev Finsler.BorelLoop Finsler.RightIntervalCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def timeSwap (Y : TopCat.{0}) : TopCat.of (ClosedInterval × Y) ⟶ space Y :=
  TopCat.ofHom ⟨fun z => (z.2, ULift.up z.1), by fun_prop⟩

def firstTime (n : ℕ) : space (Loops n) ⟶ SelfCutThomCocycle.parameters n :=
  TopCat.ofHom ⟨fun z => (z.2.down, z.1), by fun_prop⟩

def rawModel (n : ℕ) : Loops n ⊗ TopCat.of (ClosedInterval × TopCat.I.{0}) ⟶
    NativeSequentialSupportedStages.source n :=
  TopCat.ofHom ⟨fun z => ((z.2.2.down, z.1), z.2.1), by fun_prop⟩

theorem first_prism (n q : ℕ) : SelfCutTimePrism.prism n q =
    TimeTriangleSplit.interval (Loops n) q ≫ (push (firstTime n)).f (q + 1) := by
  rw [SelfCutTimePrism.prism, SelfCutTimePrism.chainHomotopy, ← TimeShuffleComparison.rectangle_eq_prism]
  rfl

theorem product_square (m : ℕ) :
    (SingularTimeCylinderMaps.cylinder (Loops (m + 1)) TopCat.I).h ≫ rawModel (m + 1) =
      (firstTime (m + 1) ▷ TopCat.I) ≫ NativeIntervalGHTests.rawSource m := rfl

theorem time_square (n : ℕ) : (Loops n ◁ timeSwap TopCat.I) ≫ NativeRawTimeSquareBoundary.squareMap n =
    rawModel n := rfl

theorem original_two_time (m p : ℕ) :
    TimeTriangleSplit.interval (Loops (m + 1)) p ≫
      ((SingularTimeCylinderMaps.cylinder (Loops (m + 1)) TopCat.I).toSSet.chainComplexMap coeff).hom (p + 1) (p + 2) ≫
        (push (rawModel (m + 1))).f (p + 2) =
    SelfCutTimePrism.prism (m + 1) p ≫ TimeTriangleSplit.interval (NativeIntervalGHTests.base m) (p + 1) ≫
      (push (NativeIntervalGHTests.rawSource m)).f (p + 2) := by
  rw [first_prism]
  simp only [Category.assoc]
  have hn := RightIntervalCochain.naturality (firstTime (m + 1)) (p + 1)
  rw [← Category.assoc ((push (firstTime (m + 1))).f (p + 1))
    (TimeTriangleSplit.interval (NativeIntervalGHTests.base m) (p + 1)), hn]
  rw [← TimeShuffleComparison.rectangle_eq_prism]
  unfold TimeShuffleComparison.rectangle
  have he := congrArg (fun f => (push f).f (p + 2)) (product_square m)
  simp only [push_comp, HomologicalComplex.comp_f] at he
  change _ ≫ (TimeTriangleSplit.interval (space (Loops (m + 1))) (p + 1) ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rw [he]

end
end Finsler.TwoTimeSquareCoordinates
