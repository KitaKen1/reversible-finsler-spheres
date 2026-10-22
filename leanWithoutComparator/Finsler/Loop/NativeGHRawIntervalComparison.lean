module

public import Finsler.Loop.NativeGHProductFaces
public import Finsler.Loop.RightIntervalCoboundary

/-! Combine the actual cap/interval order correction with the product
cover/raw-source correction. The SAME explicit parameter primitive
compares the original sequential cap/time expression with the raw
interleaved operation after the genuine interval. Both original outer
parameter endpoints vanish, ready for the original first time prism. -/
@[expose] public section
namespace Finsler.NativeGHRawIntervalComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

def correction := RightIntervalCoboundary.primitive (base m) (m + index m a b k side)
  (NativeGHProductPullback.primitive m hm F a b k E side)

def rawInterval : singularCochainGroup (ZMod 2) (base m) (m + index m a b k side + 1) := TimeTriangleSplit.interval (base m) (m + index m a b k side + 1) ≫
  NativeGHProductPullback.originalValue m hm F a b k E side

def primitive := NativeGHIntervalOrder.primitive m hm F a b k E side + correction m hm F a b k E side

theorem correction_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (base m) (m + index m a b k side) (correction m hm F a b k E side) =
    NativeGHIntervalOrder.after m hm F a b k E side - rawInterval m hm F a b k E side := by
  have h := RightIntervalCoboundary.comparison (base m) (m + index m a b k side)
    (NativeGHProductPullback.primitive m hm F a b k E side)
    (NativeGHProductPullback.productValue m hm F a b k E side)
    (NativeGHProductPullback.originalValue m hm F a b k E side)
    (NativeGHProductPullback.boundary m hm F a b k E side hE)
    (NativeGHProductFaces.primitive_endpoint m hm F a b k E side 0 (Or.inl rfl))
    (NativeGHProductFaces.primitive_endpoint m hm F a b k E side 1 (Or.inr rfl))
  rw [NativeGHProductPullback.interval_product] at h
  exact h

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (base m) (m + index m a b k side) (primitive m hm F a b k E side) =
    NativeGHIntervalOrder.before m hm F a b k E side - rawInterval m hm F a b k E side := by
  change ((cochainCxZMod2 (base m)).d _ _).hom (_ + _) = _
  rw [map_add]
  change cochainCoboundary (ZMod 2) (base m) _ (NativeGHIntervalOrder.primitive m hm F a b k E side) +
    cochainCoboundary (ZMod 2) (base m) _ (correction m hm F a b k E side) = _
  rw [NativeGHIntervalOrder.boundary m hm F a b k E side hE, correction_boundary m hm F a b k E side hE]
  abel

theorem correction_endpoint (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (m + index m a b k side)
      (correction m hm F a b k E side) = 0 :=
  RightIntervalCoboundary.primitive_pullback_zero _ _ _
    (NativeGHProductFaces.primitive_outer_endpoint m hm F a b k E side t ht)

theorem primitive_endpoint (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (m + index m a b k side)
      (primitive m hm F a b k E side) = 0 := by
  change ((singularCochainComplexZMod2.map (SelfCutThomCocycle.atTime (m + 1) t).op).f _).hom (_ + _) = 0
  rw [map_add]
  change cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) _
      (NativeGHIntervalOrder.primitive m hm F a b k E side) +
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) _ (correction m hm F a b k E side) = 0
  rw [NativeGHIntervalOrder.primitive_endpoint m hm F a b k E side t ht,
    correction_endpoint m hm F a b k E side t ht, add_zero]

end
end Finsler.NativeGHRawIntervalComparison
