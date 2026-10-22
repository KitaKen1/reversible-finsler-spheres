module

public import Finsler.Loop.NativeOrderedProductProjection
public import Finsler.Loop.NativeGraphPointSwapClass
public import Finsler.Loop.CupTripleReorder
public import Finsler.Loop.TripleCupCrossPairing

/-! Evaluate the ACTUAL graph class on both remaining ordered inputs.
Keep the original LEFT-associated cross products S,E,S and E,S,S.
Only cup products are reordered; no singular-cross associativity or
source-permutation invariance is assumed. -/
@[expose] public section
namespace Finsler.NativeOrderedProductScalars
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativePairRelativeSphereTransport Finsler.NativeExplicitGraphClass
open Finsler.MeridianOrderedSweepInputs Finsler.NativeOrderedProductProjection
open Finsler.TripleCupCrossPairing
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem first_pullback {X : TopCat.{0}} (m : ℕ) (P : Sphere (m + 1))
    (f : X ⟶ graphSpace P) (g : X ⟶ S (m + 1))
    (h : f ≫ NativeExplicitGraphCap.first P = g) :
    (cohPullback f (m + 1)).hom (firstTop m P) =
      (cohPullback g (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega)) :=
  (Cup.pullback_comp f (NativeExplicitGraphCap.first P) (m + 1) _).symm.trans
    (congrArg (fun k => (cohPullback k (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))) h)

theorem second_pullback {X : TopCat.{0}} (m : ℕ) (P : Sphere (m + 1))
    (f : X ⟶ graphSpace P) (g : X ⟶ S (m + 1))
    (h : f ≫ (snd (S (m + 1)) (NativeExplicitGraphCap.tail P) ≫ NativeExplicitGraphCap.second P) = g) :
    (cohPullback f (m + 1)).hom (secondTop m P) =
      (cohPullback g (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega)) := by
  let top := SphereTopClass.topClass (m + 1) (by omega)
  let k : graphSpace P ⟶ S (m + 1) := snd (S (m + 1)) (NativeExplicitGraphCap.tail P) ≫ NativeExplicitGraphCap.second P
  have hk : secondTop m P = (cohPullback k (m + 1)).hom top :=
    (Cup.pullback_comp (snd (S (m + 1)) (NativeExplicitGraphCap.tail P))
      (NativeExplicitGraphCap.second P) (m + 1) top).symm
  exact (congrArg (cohPullback f (m + 1)).hom hk).trans
    ((Cup.pullback_comp f k (m + 1) top).symm.trans
      (congrArg (fun l => (cohPullback l (m + 1)).hom top) h))

theorem remaining_pullback {X : TopCat.{0}} (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    (f : X ⟶ graphSpace P) (g : X ⟶ E P) (h : f ≫ NativeExplicitGraphCap.remaining P = g) :
    (cohPullback f m).hom (remainingClass m P v₀) =
      (cohPullback g m).hom (LocalNativeBallPrimitive.remainingClass m P v₀) :=
  (Cup.pullback_comp f (NativeExplicitGraphCap.remaining P) m _).symm.trans
    (congrArg (fun l => (cohPullback l m).hom (LocalNativeBallPrimitive.remainingClass m P v₀)) h)

theorem pullback02 (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (toGraph02 P) (3 * m + 2)).hom
      (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀)) =
    tripleClass (S (m + 1)) (E P) (S (m + 1)) (m + 1) m (m + 1) (2 * m + 1) (3 * m + 2)
      (by omega) (by omega) (SphereTopClass.topClass (m + 1) (by omega))
      (LocalNativeBallPrimitive.remainingClass m P v₀) (SphereTopClass.topClass (m + 1) (by omega)) := by
  rw [NativeGraphPointSwapClass.explicit_normal]
  unfold NativeGraphPointSwapClass.normalClass
  rw [CupAtDegree.naturality, CupAtDegree.naturality,
    first_pullback m P (toGraph02 P) (firstProjection (S (m + 1)) (E P) (S (m + 1))) rfl,
    second_pullback m P (toGraph02 P) (thirdProjection (S (m + 1)) (E P) (S (m + 1))) rfl,
    remaining_pullback m P v₀ (toGraph02 P) (secondProjection (S (m + 1)) (E P) (S (m + 1))) rfl]
  exact (CupTripleReorder.swap_last _ (m + 1) m (m + 1) (2 * m + 2) (2 * m + 1) (2 * m + 1) (3 * m + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) _ _ _).trans
    (expanded _ _ _ _ _ _ _ _ _ _ _ _ _).symm

theorem pullback12 (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (toGraph12 P) (3 * m + 2)).hom
      (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀)) =
    tripleClass (E P) (S (m + 1)) (S (m + 1)) m (m + 1) (m + 1) (2 * m + 1) (3 * m + 2)
      (by omega) (by omega) (LocalNativeBallPrimitive.remainingClass m P v₀)
      (SphereTopClass.topClass (m + 1) (by omega)) (SphereTopClass.topClass (m + 1) (by omega)) := by
  rw [NativeGraphPointSwapClass.explicit_normal]
  unfold NativeGraphPointSwapClass.normalClass
  rw [CupAtDegree.naturality, CupAtDegree.naturality,
    first_pullback m P (toGraph12 P) (secondProjection (E P) (S (m + 1)) (S (m + 1))) rfl,
    second_pullback m P (toGraph12 P) (thirdProjection (E P) (S (m + 1)) (S (m + 1))) rfl,
    remaining_pullback m P v₀ (toGraph12 P) (firstProjection (E P) (S (m + 1)) (S (m + 1))) rfl]
  exact (CupTripleReorder.rotate_last _ m (m + 1) (m + 1) (2 * m + 2) (2 * m + 1) (3 * m + 2)
    (by omega) (by omega) (by omega) (by omega) _ _ _).trans
    (expanded _ _ _ _ _ _ _ _ _ _ _ _ _).symm

theorem scalar02_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (graphSpace P) (3 * m + 2)).hom
      (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀))
      ((homologyPushZMod2 (toGraph02 P) (3 * m + 2)).hom (class02 m hm P)) = 1 := by
  rw [CupAtDegreeCrossPairing.pairing_push, pullback02]
  exact (triple_pairing (S (m + 1)) (E P) (S (m + 1)) (m + 1) m (m + 1) (2 * m + 1) (3 * m + 2)
    (by omega) (by omega) (SphereTopClass.topClass (m + 1) (by omega))
    (LocalNativeBallPrimitive.remainingClass m P v₀) (SphereTopClass.topClass (m + 1) (by omega))
    (SphereUnitCandidate.fundamental (m + 1) (by omega)) (MeridianEquatorHomology.fundamental m hm P)
    (SphereUnitCandidate.fundamental (m + 1) (by omega))).trans
    (by rw [SphereUnitCandidate.top_evaluation_one, NativeGraphFundamentalScalar.remaining_pairing, one_mul, one_mul])

theorem scalar12_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (graphSpace P) (3 * m + 2)).hom
      (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀))
      ((homologyPushZMod2 (toGraph12 P) (3 * m + 2)).hom (class12 m hm P)) = 1 := by
  rw [CupAtDegreeCrossPairing.pairing_push, pullback12]
  exact (triple_pairing (E P) (S (m + 1)) (S (m + 1)) m (m + 1) (m + 1) (2 * m + 1) (3 * m + 2)
    (by omega) (by omega) (LocalNativeBallPrimitive.remainingClass m P v₀)
    (SphereTopClass.topClass (m + 1) (by omega)) (SphereTopClass.topClass (m + 1) (by omega))
    (MeridianEquatorHomology.fundamental m hm P) (SphereUnitCandidate.fundamental (m + 1) (by omega))
    (SphereUnitCandidate.fundamental (m + 1) (by omega))).trans
    (by rw [SphereUnitCandidate.top_evaluation_one, NativeGraphFundamentalScalar.remaining_pairing, one_mul, one_mul])

end
end Finsler.NativeOrderedProductScalars
