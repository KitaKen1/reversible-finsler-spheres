module

public import Finsler.Loop.OrderedSquareNormalizedPrism

/-! The two ACTUAL raw-clock square cochains differ by an explicit
source coboundary after normalizing a closed diagonal-relative input.
Thus their values agree on EVERY actual source cycle. The original
double-cut Thom/cap input and its diagonal support remain separate. -/
@[expose] public section
namespace Finsler.OrderedClockCycleComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def primitive (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3)) :
    singularCochainGroup (ZMod 2) X p :=
  (OrderedDoubleCutSquareChain.insertion X p ≫
    OrderedDoubleCutClockPrism.prism X OrderedDoubleCutTimes.leftHomotopy (p + 2) ≫
      SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) -
  (OrderedDoubleCutSquareChain.insertion X p ≫
    OrderedDoubleCutClockPrism.prism X OrderedDoubleCutTimes.rightHomotopy (p + 2) ≫
      SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ)

theorem comparison_boundary (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3))
    (hφ : cochainCoboundary (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ = 0)
    (hd : cochainPullback (X ◁ OrderedDoubleCutTriangle.diagonal) (p + 3) φ = 0) :
    cochainCoboundary (ZMod 2) X p (primitive X p φ) =
      OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.leftClock) (p + 3)
          (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) -
      OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.rightClock) (p + 3)
          (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) := by
  have h := OrderedDoubleCutClockPrism.two_clock_relation X p
    (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ)
    (SingularNormalization.normalize_closed _ _ φ hφ)
    (SingularNormalization.normalize_supported _ _ φ hd)
  rw [OrderedSquareNormalizedPrism.left_square_error_zero,
    OrderedSquareNormalizedPrism.right_square_error_zero, add_zero, add_zero] at h
  change (chains X).d (p + 1) p ≫ primitive X p φ = _
  simpa only [primitive, OrderedDoubleCutClockPrism.sourceError, Preadditive.comp_sub,
    Category.assoc] using h.symm

theorem cycles_equal (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3))
    (hφ : cochainCoboundary (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ = 0)
    (hd : cochainPullback (X ◁ OrderedDoubleCutTriangle.diagonal) (p + 3) φ = 0) :
    (chains X).iCycles (p + 1) ≫ OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.leftClock) (p + 3)
          (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) =
    (chains X).iCycles (p + 1) ≫ OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.rightClock) (p + 3)
          (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) := by
  have h := congrArg (fun k => (chains X).iCycles (p + 1) ≫ k)
    (comparison_boundary X p φ hφ hd)
  change (chains X).iCycles (p + 1) ≫ ((chains X).d (p + 1) p ≫ primitive X p φ) = _ at h
  simp only [Preadditive.comp_sub, ← Category.assoc, (chains X).iCycles_d, zero_comp] at h
  exact sub_eq_zero.mp h.symm

theorem cycle_values_equal (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3))
    (hφ : cochainCoboundary (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ = 0)
    (hd : cochainPullback (X ◁ OrderedDoubleCutTriangle.diagonal) (p + 3) φ = 0)
    (c : coeff ⟶ (chains X).X (p + 1)) (hc : c ≫ (chains X).d (p + 1) p = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.leftClock) (p + 3)
          (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) =
    c ≫ OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.rightClock) (p + 3)
          (SingularNormalization.normalize (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ) := by
  have h := congrArg (fun k => c ≫ k) (comparison_boundary X p φ hφ hd)
  change c ≫ ((chains X).d (p + 1) p ≫ primitive X p φ) = _ at h
  simp only [Preadditive.comp_sub, ← Category.assoc, hc, zero_comp] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.OrderedClockCycleComparison
