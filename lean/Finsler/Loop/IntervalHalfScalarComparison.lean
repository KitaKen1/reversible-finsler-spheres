module

public import Finsler.Loop.SingularRightFullBoundary
public import Finsler.Loop.RightIntervalCochain

/-! The SAME affine interval triangle compares the full canonical
interval with its two actual halves on arbitrary input chains. The
source boundary is retained as an explicit scalar primitive. -/
@[expose] public section
namespace Finsler.IntervalHalfScalarComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RightIntervalCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def halfMap (side : Bool) : TopCat.I.{0} ⟶ TopCat.I.{0} :=
  if side then IntervalTriangle.secondMap else IntervalTriangle.firstMap

theorem full_boundary (X : TopCat.{0}) (p : ℕ) :
    TimeTriangleSplit.triangle X (p + 1) ≫ (chains (space X)).d (p + 3) (p + 2) =
      (chains X).d (p + 1) p ≫ TimeTriangleSplit.triangle X p +
      (TimeTriangleSplit.interval X (p + 1) ≫ (push (X ◁ halfMap true)).f (p + 2)) +
      TimeTriangleSplit.interval X (p + 1) +
      (TimeTriangleSplit.interval X (p + 1) ≫ (push (X ◁ halfMap false)).f (p + 2)) := by
  have h := SingularRightFullBoundary.rightChain_boundary_two X TopCat.I p
    ((TopCat.toSSet.obj TopCat.I).ιChainComplex IntervalTriangle.triangle)
  rw [IntervalTriangle.triangle_boundary] at h
  simpa only [SingularRightBoundary.rightChain_add, SingularRightNaturality.rightChain_map_simplex,
    SingularRightBoundary.rightChain_simplex, TimeTriangleSplit.triangle, TimeTriangleSplit.interval,
    halfMap, Bool.false_eq_true, ite_false, ite_true, add_assoc] using h

def primitive (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 2)) :
    singularCochainGroup (ZMod 2) X p := TimeTriangleSplit.triangle X p ≫ T

def value (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 2)) :
    singularCochainGroup (ZMod 2) X (p + 1) := TimeTriangleSplit.interval X (p + 1) ≫ T

def halfValue (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 2)) (side : Bool) :
    singularCochainGroup (ZMod 2) X (p + 1) :=
  TimeTriangleSplit.interval X (p + 1) ≫ cochainPullback (X ◁ halfMap side) (p + 2) T

private theorem neg_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) : -v = v := by
  have h := BorelCochain.two_eq_zero_of_mod v
  calc
    -v = -v + (v + v) := by rw [h, add_zero]
    _ = v := by abel

theorem boundary (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 2))
    (hT : cochainCoboundary (ZMod 2) (space X) (p + 2) T = 0) :
    cochainCoboundary (ZMod 2) X p (primitive X p T) =
      value X p T - halfValue X p T false - halfValue X p T true := by
  have h := congrArg (fun f => f ≫ T) (full_boundary X p)
  have hz : (chains (space X)).d (p + 3) (p + 2) ≫ T = 0 := hT
  simp only [Preadditive.add_comp, Category.assoc, hz, comp_zero] at h
  change 0 = cochainCoboundary (ZMod 2) X p (primitive X p T) +
    halfValue X p T true + value X p T + halfValue X p T false at h
  have hn := neg_self (value X p T)
  calc
    _ = (cochainCoboundary (ZMod 2) X p (primitive X p T) + halfValue X p T true + value X p T +
        halfValue X p T false) - halfValue X p T true - value X p T - halfValue X p T false := by abel
    _ = -halfValue X p T true - value X p T - halfValue X p T false := by rw [← h, zero_sub]
    _ = _ := by simp only [sub_eq_add_neg]; rw [hn]; abel

theorem boundary_one_half (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (space X) (p + 2))
    (hT : cochainCoboundary (ZMod 2) (space X) (p + 2) T = 0) (side : Bool)
    (hz : cochainPullback (X ◁ halfMap (!side)) (p + 2) T = 0) :
    cochainCoboundary (ZMod 2) X p (primitive X p T) = value X p T - halfValue X p T side := by
  have hhalf : halfValue X p T (!side) = 0 := by rw [halfValue, hz, comp_zero]
  rw [boundary X p T hT]
  cases side <;> simp only [Bool.not_false, Bool.not_true] at hhalf ⊢
  · rw [hhalf, sub_zero]
  · rw [hhalf, sub_zero]

end
end Finsler.IntervalHalfScalarComparison
