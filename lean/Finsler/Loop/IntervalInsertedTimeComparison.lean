module

public import Finsler.Loop.SingularTimeFullComparison
public import Finsler.Loop.SingularTimeDoubleNaturality
public import Finsler.Loop.RightTensorInsertion
public import Finsler.Loop.CanonicalIntervalChainBoundary

/-! Compare product-time and tensor-time AFTER an actual interval has
already been inserted. Its endpoints are discharged through the SAME
natural double prism; the original source boundary remains explicit.
An interval-inserted input is never declared to be an absolute cycle. -/
@[expose] public section
namespace Finsler.IntervalInsertedTimeComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.IntervalSobolev Finsler.SupportedCapNaturality
open Finsler.CanonicalIntervalChainBoundary
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

abbrev target (X : TopCat.{0}) := X ⊗ TopCat.of (ClosedInterval × TopCat.I.{0})

theorem endpoint_zero (X : TopCat.{0}) (N : ℕ) (t : ClosedInterval)
    (T : singularCochainGroup (ZMod 2) (target X) (N + 2))
    (hT : cochainPullback (X ◁ SingularTimeDoubleNaturality.timeMap (endpoint t)) (N + 2) T = 0) :
    RightTensorInsertion.insert (chains X) (chains TopCat.I) N 0
      (pointChain ≫ (push (endpoint t)).f 0) ≫
        SingularTimeModelComparison.doublePrism X TopCat.I N ≫ T = 0 := by
  rw [← RightTensorInsertion.naturality]
  simp only [Category.assoc]
  have h := congrArg (fun f => RightTensorInsertion.insert (chains X) (chains point) N 0 pointChain ≫ f)
    (SingularTimeDoubleNaturality.scalar_zero X (endpoint t) N T hT)
  simp only [comp_zero] at h
  exact h

theorem endpoints_zero (X : TopCat.{0}) (N : ℕ)
    (T : singularCochainGroup (ZMod 2) (target X) (N + 2))
    (h₀ : cochainPullback (X ◁ SingularTimeDoubleNaturality.timeMap (endpoint 0)) (N + 2) T = 0)
    (h₁ : cochainPullback (X ◁ SingularTimeDoubleNaturality.timeMap (endpoint 1)) (N + 2) T = 0) :
    RightTensorInsertion.insert (chains X) (chains TopCat.I) N 0
      (intervalChain ≫ (chains TopCat.I).d 1 0) ≫
        SingularTimeModelComparison.doublePrism X TopCat.I N ≫ T = 0 := by
  have hs (a b : coeff ⟶ (chains TopCat.I).X 0) :
      RightTensorInsertion.insert (chains X) (chains TopCat.I) N 0 (a - b) =
      RightTensorInsertion.insert (chains X) (chains TopCat.I) N 0 a -
      RightTensorInsertion.insert (chains X) (chains TopCat.I) N 0 b := by
    have hl : (chains X).X N ◁ (a - b) = (chains X).X N ◁ a - (chains X).X N ◁ b :=
      (tensorLeft ((chains X).X N)).map_sub
    simp only [RightTensorInsertion.insert, hl, Preadditive.comp_sub, Preadditive.sub_comp]
  rw [CanonicalIntervalChainBoundary.boundary, hs, Preadditive.sub_comp,
    endpoint_zero X N 1 T h₁, endpoint_zero X N 0 T h₀, sub_self]

variable (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) (target X) (p + 3))

def primitive : singularCochainGroup (ZMod 2) X p :=
  -(RightTensorInsertion.insert (chains X) (chains TopCat.I) p 1 intervalChain ≫
    SingularTimeModelComparison.doublePrism X TopCat.I (p + 1) ≫ T)

def productValue : singularCochainGroup (ZMod 2) X (p + 1) :=
  RightTensorInsertion.insert (chains X) (chains TopCat.I) (p + 1) 1 intervalChain ≫
    (SmallRectangleCross.ambient X TopCat.I).f (p + 2) ≫
      ((SingularTimeCylinderMaps.cylinder X TopCat.I).toSSet.chainComplexMap coeff).hom (p + 2) (p + 3) ≫ T

def tensorValue : singularCochainGroup (ZMod 2) X (p + 1) :=
  RightTensorInsertion.insert (chains X) (chains TopCat.I) (p + 1) 1 intervalChain ≫
    (FullTensorTimePrism.prism X TopCat.I).hom (p + 2) (p + 3) ≫
      (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × TopCat.I))).f (p + 3) ≫ T

theorem boundary (hT : cochainCoboundary (ZMod 2) (target X) (p + 3) T = 0)
    (h₀ : cochainPullback (X ◁ SingularTimeDoubleNaturality.timeMap (endpoint 0)) (p + 3) T = 0)
    (h₁ : cochainPullback (X ◁ SingularTimeDoubleNaturality.timeMap (endpoint 1)) (p + 3) T = 0) :
    cochainCoboundary (ZMod 2) X p (primitive X p T) = productValue X p T - tensorValue X p T := by
  have h := congrArg (fun f => RightTensorInsertion.insert (chains X) (chains TopCat.I) (p + 1) 1 intervalChain ≫ f)
    (SingularTimeFullComparison.scalar_comparison X TopCat.I (p + 1) T hT)
  rw [Preadditive.comp_neg, ← Category.assoc _ ((chains X ⊗ chains TopCat.I).d (p + 2) (p + 1)),
    RightTensorInsertion.boundary_one, Preadditive.add_comp, Category.assoc,
    endpoints_zero X (p + 1) T h₀ h₁, add_zero] at h
  simp only [SingularTimeFullComparison.difference, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc] at h
  change (chains X).d (p + 1) p ≫ (-(RightTensorInsertion.insert _ _ p 1 intervalChain ≫
    SingularTimeModelComparison.doublePrism X TopCat.I (p + 1) ≫ T)) = _
  rw [Preadditive.comp_neg]
  exact h.symm

theorem cycle_values_eq (hT : cochainCoboundary (ZMod 2) (target X) (p + 3) T = 0)
    (h₀ : cochainPullback (X ◁ SingularTimeDoubleNaturality.timeMap (endpoint 0)) (p + 3) T = 0)
    (h₁ : cochainPullback (X ◁ SingularTimeDoubleNaturality.timeMap (endpoint 1)) (p + 3) T = 0)
    (c : coeff ⟶ (chains X).X (p + 1)) (hc : c ≫ (chains X).d (p + 1) p = 0) :
    c ≫ productValue X p T = c ≫ tensorValue X p T := by
  have h := congrArg (fun f => c ≫ f) (boundary X p T hT h₀ h₁)
  change c ≫ ((chains X).d (p + 1) p ≫ primitive X p T) = _ at h
  rw [← Category.assoc c, hc, zero_comp, Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.IntervalInsertedTimeComparison
