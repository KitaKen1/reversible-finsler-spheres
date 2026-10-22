module

public import Finsler.Loop.OrderedDoubleCutSquareChain
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! Clock comparison on the ACTUAL shuffle square. Closed cochains
remove the OUTPUT boundary only. Source-boundary and square-boundary
prism terms remain explicitly; no vanishing is assumed or inferred
from pointwise boundary fixation. -/
@[expose] public section
namespace Finsler.OrderedDoubleCutClockPrism
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

variable {f g : OrderedDoubleCutTimes.square ⟶ OrderedDoubleCutTimes.space}

def lift (X : TopCat.{0}) (H : TopCat.Homotopy f g) : TopCat.Homotopy (X ◁ f) (X ◁ g) where
  toFun z := (z.2.1, H (z.1, z.2.2))
  continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
    (H.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left z := congrArg (fun y => (z.1, y)) (H.map_zero_left z.2)
  map_one_left z := congrArg (fun y => (z.1, y)) (H.map_one_left z.2)

def prism (X : TopCat.{0}) (H : TopCat.Homotopy f g) (q : ℕ) :=
  ((lift X H).toSSet.chainComplexMap coeff).hom q (q + 1)

theorem boundary (X : TopCat.{0}) (H : TopCat.Homotopy f g) (q : ℕ) :
    (push (X ◁ f)).f (q + 1) - (push (X ◁ g)).f (q + 1) =
      (chains (X ⊗ OrderedDoubleCutTimes.square)).d (q + 1) q ≫ prism X H q +
      prism X H (q + 1) ≫ (chains (X ⊗ OrderedDoubleCutTimes.space)).d (q + 2) (q + 1) := by
  let K := (lift X H).toSSet.chainComplexMap coeff
  have h := K.comm (q + 1)
  have he : (chains (X ⊗ OrderedDoubleCutTimes.square)).d (q + 1) q ≫ K.hom q (q + 1) +
      K.hom (q + 1) (q + 2) ≫ (chains (X ⊗ OrderedDoubleCutTimes.space)).d (q + 2) (q + 1) =
      (push (X ◁ f)).f (q + 1) - (push (X ◁ g)).f (q + 1) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, push] using h.symm
  exact he.symm

def sourceError (X : TopCat.{0}) (H : TopCat.Homotopy f g) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3)) :=
  (chains X).d (p + 1) p ≫ OrderedDoubleCutSquareChain.insertion X p ≫ prism X H (p + 2) ≫ φ

def squareError (X : TopCat.{0}) (H : TopCat.Homotopy f g) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3)) :=
  SingularRightBoundary.rightChain X OrderedDoubleCutTimes.square (p + 1) 1
    (OrderedDoubleCutSquareShuffle.squareChain ≫ (chains OrderedDoubleCutTimes.square).d 2 1) ≫
      prism X H (p + 2) ≫ φ

theorem closed_clock_relation (X : TopCat.{0}) (H : TopCat.Homotopy f g) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3))
    (hφ : cochainCoboundary (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ = 0) :
    OrderedDoubleCutSquareChain.insertion X (p + 1) ≫ cochainPullback (X ◁ f) (p + 3) φ -
      OrderedDoubleCutSquareChain.insertion X (p + 1) ≫ cochainPullback (X ◁ g) (p + 3) φ =
    sourceError X H p φ + squareError X H p φ := by
  change OrderedDoubleCutSquareChain.insertion X (p + 1) ≫ ((push (X ◁ f)).f (p + 3) ≫ φ) -
    OrderedDoubleCutSquareChain.insertion X (p + 1) ≫ ((push (X ◁ g)).f (p + 3) ≫ φ) = _
  have h := congrArg (fun k => OrderedDoubleCutSquareChain.insertion X (p + 1) ≫ k ≫ φ)
    (boundary X H (p + 2))
  change (chains (X ⊗ OrderedDoubleCutTimes.space)).d (p + 4) (p + 3) ≫ φ = 0 at hφ
  simp only [Preadditive.comp_sub, Preadditive.sub_comp,
    Preadditive.add_comp, Category.assoc, hφ, comp_zero, add_zero] at h
  have hb := congrArg (fun k => k ≫ prism X H (p + 2) ≫ φ)
    (OrderedDoubleCutSquareChain.full_boundary X p)
  have he := h.trans hb
  simpa only [Preadditive.add_comp, Category.assoc, sourceError, squareError] using he

theorem two_clock_relation (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3))
    (hφ : cochainCoboundary (ZMod 2) (X ⊗ OrderedDoubleCutTimes.space) (p + 3) φ = 0)
    (hd : cochainPullback (X ◁ OrderedDoubleCutTriangle.diagonal) (p + 3) φ = 0) :
    OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.leftClock) (p + 3) φ -
      OrderedDoubleCutSquareChain.insertion X (p + 1) ≫
        cochainPullback (X ◁ OrderedDoubleCutTimes.rightClock) (p + 3) φ =
    (sourceError X OrderedDoubleCutTimes.leftHomotopy p φ +
      squareError X OrderedDoubleCutTimes.leftHomotopy p φ) -
    (sourceError X OrderedDoubleCutTimes.rightHomotopy p φ +
      squareError X OrderedDoubleCutTimes.rightHomotopy p φ) := by
  have hl := closed_clock_relation X OrderedDoubleCutTimes.leftHomotopy p φ hφ
  have hr := closed_clock_relation X OrderedDoubleCutTimes.rightHomotopy p φ hφ
  have ha := OrderedDoubleCutSquareChain.affine_cochain_comparison X (p + 1) φ hd
  rw [← hl, ← hr, ← ha]
  abel

end
end Finsler.OrderedDoubleCutClockPrism
