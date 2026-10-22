module

public import Finsler.Loop.NativeCutPointSwap
public import Finsler.Loop.NativeGraphFundamentalScalar

/-! The actual GLOBAL graph cap class is invariant under exchanging
its two sphere points. Normalize to (firstTop cup secondTop) cup remaining;
the first sphere top square is zero and F2 cup commutativity exchanges
the two top factors. This computes the swapped ACTUAL class, without
assuming a symmetric cochain representative or cross associativity. -/
@[expose] public section
namespace Finsler.NativeGraphPointSwapClass
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativePairRelativeSphereTransport Finsler.NativeExplicitGraphClass
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

theorem swap_first (m : ℕ) (P : Sphere (m + 1)) :
    (cohPullback (NativeCutPointSwap.graphSwap P) (m + 1)).hom (firstTop m P) = secondTop m P := by
  have hf : NativeCutPointSwap.graphSwap P ≫ NativeExplicitGraphCap.first P =
      snd (BorelEvaluation.sphere (m + 1)) (NativeExplicitGraphCap.tail P) ≫ NativeExplicitGraphCap.second P := rfl
  exact (Cup.pullback_comp (NativeCutPointSwap.graphSwap P) (NativeExplicitGraphCap.first P) (m + 1) _).symm.trans
    ((congrArg (fun f => (cohPullback f (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))) hf).trans
      (Cup.pullback_comp (snd (BorelEvaluation.sphere (m + 1)) (NativeExplicitGraphCap.tail P))
        (NativeExplicitGraphCap.second P) (m + 1) _))

theorem swap_second (m : ℕ) (P : Sphere (m + 1)) :
    (cohPullback (NativeCutPointSwap.graphSwap P) (m + 1)).hom (secondTop m P) = firstTop m P := by
  let g : graphSpace P ⟶ BorelEvaluation.sphere (m + 1) :=
    snd (BorelEvaluation.sphere (m + 1)) (NativeExplicitGraphCap.tail P) ≫ NativeExplicitGraphCap.second P
  let top := SphereTopClass.topClass (m + 1) (by omega)
  have hg : secondTop m P = (cohPullback g (m + 1)).hom top :=
    (Cup.pullback_comp (X := graphSpace P) (snd (BorelEvaluation.sphere (m + 1)) (NativeExplicitGraphCap.tail P))
      (NativeExplicitGraphCap.second P) (m + 1) top).symm
  have hf : NativeCutPointSwap.graphSwap P ≫ g = NativeExplicitGraphCap.first P := rfl
  exact (congrArg (cohPullback (NativeCutPointSwap.graphSwap P) (m + 1)).hom hg).trans
    ((Cup.pullback_comp (NativeCutPointSwap.graphSwap P) g (m + 1) top).symm.trans
      (congrArg (fun f => (cohPullback f (m + 1)).hom top) hf))

theorem swap_remaining (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (NativeCutPointSwap.graphSwap P) m).hom (remainingClass m P v₀) = remainingClass m P v₀ := by
  have hf : NativeCutPointSwap.graphSwap P ≫ NativeExplicitGraphCap.remaining P = NativeExplicitGraphCap.remaining P := rfl
  exact (Cup.pullback_comp (NativeCutPointSwap.graphSwap P) (NativeExplicitGraphCap.remaining P) m
    (LocalNativeBallPrimitive.remainingClass m P v₀)).symm.trans
      (congrArg (fun f => (cohPullback f m).hom (LocalNativeBallPrimitive.remainingClass m P v₀)) hf)

def normalClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  CupAtDegree.cup (graphSpace P) (2 * m + 2) m (3 * m + 2) (by omega)
    (CupAtDegree.cup (graphSpace P) (m + 1) (m + 1) (2 * m + 2) (by omega) (firstTop m P) (secondTop m P))
    (remainingClass m P v₀)

theorem explicit_normal (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀) = normalClass m P v₀ :=
  CupAtDegree.diagonal_triple_reduction_at (graphSpace P) (m + 1) m (2 * m + 2) (3 * m + 2)
    (by omega) (NativePairDoublePrismSource.degree m) (firstTop m P) (secondTop m P) (remainingClass m P v₀)
    (NativeGraphFundamentalScalar.first_square_zero m P)

theorem normal_swap (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (NativeCutPointSwap.graphSwap P) (3 * m + 2)).hom (normalClass m P v₀) = normalClass m P v₀ := by
  unfold normalClass
  rw [CupAtDegree.naturality, CupAtDegree.naturality, swap_first, swap_second, swap_remaining]
  exact congrArg (fun a => CupAtDegree.cup (graphSpace P) (2 * m + 2) m (3 * m + 2) (by omega) a (remainingClass m P v₀))
    (CupAtDegree.comm (graphSpace P) (m + 1) (m + 1) (2 * m + 2) (by omega) (secondTop m P) (firstTop m P))

theorem actual_cast_class_swap (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (NativeCutPointSwap.graphSwap P) (3 * m + 2)).hom
      (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀)) =
      CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀) :=
  (congrArg (cohPullback (NativeCutPointSwap.graphSwap P) (3 * m + 2)).hom (explicit_normal m P v₀)).trans
    ((normal_swap m P v₀).trans (explicit_normal m P v₀).symm)

theorem actual_swapped_scalar_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (graphSpace P) (3 * m + 2)).hom
      ((cohPullback (NativeCutPointSwap.graphSwap P) (3 * m + 2)).hom
        (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀)))
      (NativeDoubleFundamentalImage.fundamentalImage m hm P) = 1 :=
  (congrArg (fun a => (kroneckerMap (graphSpace P) (3 * m + 2)).hom a
    (NativeDoubleFundamentalImage.fundamentalImage m hm P)) (actual_cast_class_swap m P v₀)).trans
      (NativeGraphFundamentalScalar.scalar_one m hm P v₀)

end
end Finsler.NativeGraphPointSwapClass
