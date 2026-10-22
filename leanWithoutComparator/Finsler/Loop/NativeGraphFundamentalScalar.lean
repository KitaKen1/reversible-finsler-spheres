module

public import Finsler.Loop.NativeExplicitGraphClass
public import Finsler.Loop.CupAtDegreeCrossPairing

/-! Direct LEFT-associated evaluation of the ACTUAL explicit graph class.
The real sphere top square vanishes. Actual cup identities and two
specified-degree CrossCupPairing evaluations give scalarONE, without
any assumption of general singular-cross associativity. -/
@[expose] public section
namespace Finsler.NativeGraphFundamentalScalar
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativePairRelativeSphereTransport Finsler.NativeExplicitGraphClass
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

abbrev S (m : ℕ) := BorelEvaluation.sphere (m + 1)
abbrev E {n : ℕ} (P : Sphere n) := TopCat.of (equator P)
abbrev leftSpace (m : ℕ) (P : Sphere (m + 1)) := (S m ⊗ S m) ⊗ E P
abbrev associator (m : ℕ) (P : Sphere (m + 1)) : leftSpace m P ⟶ graphSpace P := (α_ (S m) (S m) (E P)).hom

def pairTop (m : ℕ) :=
  CupAtDegree.cup (S m ⊗ S m) (m + 1) (m + 1) (2 * m + 2) (by omega)
    ((cohPullback (fst (S m) (S m)) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega)))
    ((cohPullback (snd (S m) (S m)) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega)))

theorem first_square_zero (m : ℕ) (P : Sphere (m + 1)) : cupZMod2 (firstTop m P) (firstTop m P) = 0 := by
  have hn := Cup.naturality (NativeExplicitGraphCap.first P) (m + 1) (m + 1)
    (SphereTopClass.topClass (m + 1) (by omega)) (SphereTopClass.topClass (m + 1) (by omega))
  exact hn.symm.trans ((congrArg (cohPullback (NativeExplicitGraphCap.first P) ((m + 1) + (m + 1))).hom
    (SphereTopClass.topClass_cup_self (m + 1) (by omega))).trans (map_zero _))

theorem first_pullback (m : ℕ) (P : Sphere (m + 1)) :
    (cohPullback (associator m P) (m + 1)).hom (firstTop m P) =
      (cohPullback (fst (S m ⊗ S m) (E P)) (m + 1)).hom
        ((cohPullback (fst (S m) (S m)) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))) := by
  have hf : associator m P ≫ NativeExplicitGraphCap.first P = fst (S m ⊗ S m) (E P) ≫ fst (S m) (S m) := by
    apply TopCat.ext
    intro z
    rfl
  exact (Cup.pullback_comp (associator m P) (NativeExplicitGraphCap.first P) (m + 1) _).symm.trans
    ((congrArg (fun f => (cohPullback f (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))) hf).trans
      (Cup.pullback_comp (fst (S m ⊗ S m) (E P)) (fst (S m) (S m)) (m + 1) _))

theorem second_pullback (m : ℕ) (P : Sphere (m + 1)) :
    (cohPullback (associator m P) (m + 1)).hom (secondTop m P) =
      (cohPullback (fst (S m ⊗ S m) (E P)) (m + 1)).hom
        ((cohPullback (snd (S m) (S m)) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))) := by
  let g : graphSpace P ⟶ S m := snd (S m) (NativeExplicitGraphCap.tail P) ≫ NativeExplicitGraphCap.second P
  let top := SphereTopClass.topClass (m + 1) (by omega)
  have hg : secondTop m P = (cohPullback g (m + 1)).hom top :=
    (Cup.pullback_comp (X := graphSpace P) (snd (S m) (NativeExplicitGraphCap.tail P))
      (NativeExplicitGraphCap.second P) (m + 1) top).symm
  have hf : associator m P ≫ g = fst (S m ⊗ S m) (E P) ≫ snd (S m) (S m) := by
    apply TopCat.ext
    intro z
    rfl
  exact (congrArg (cohPullback (associator m P) (m + 1)).hom hg).trans
    ((Cup.pullback_comp (associator m P) g (m + 1) top).symm.trans
      ((congrArg (fun f => (cohPullback f (m + 1)).hom top) hf).trans
        (Cup.pullback_comp (fst (S m ⊗ S m) (E P)) (snd (S m) (S m)) (m + 1) top)))

theorem remaining_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (associator m P) m).hom (remainingClass m P v₀) =
      (cohPullback (snd (S m ⊗ S m) (E P)) m).hom (LocalNativeBallPrimitive.remainingClass m P v₀) := by
  have hf : associator m P ≫ NativeExplicitGraphCap.remaining P = snd (S m ⊗ S m) (E P) := by
    apply TopCat.ext
    intro z
    rfl
  exact (Cup.pullback_comp (associator m P) (NativeExplicitGraphCap.remaining P) m
    (LocalNativeBallPrimitive.remainingClass m P v₀)).symm.trans
      (congrArg (fun f => (cohPullback f m).hom (LocalNativeBallPrimitive.remainingClass m P v₀)) hf)

theorem explicit_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (associator m P) (3 * m + 2)).hom
      (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀)) =
    CupAtDegree.cup (leftSpace m P) (2 * m + 2) m (3 * m + 2) (by omega)
      ((cohPullback (fst (S m ⊗ S m) (E P)) (2 * m + 2)).hom (pairTop m))
      ((cohPullback (snd (S m ⊗ S m) (E P)) m).hom (LocalNativeBallPrimitive.remainingClass m P v₀)) := by
  have hs := CupAtDegree.diagonal_triple_reduction_at (graphSpace P) (m + 1) m (2 * m + 2) (3 * m + 2)
    (by omega) (NativePairDoublePrismSource.degree m) (firstTop m P) (secondTop m P) (remainingClass m P v₀)
    (first_square_zero m P)
  have he := congrArg (cohPullback (associator m P) (3 * m + 2)).hom hs
  conv at he =>
    rhs
    rw [CupAtDegree.naturality, CupAtDegree.naturality, first_pullback, second_pullback, remaining_pullback]
  have hp := CupAtDegree.naturality (fst (S m ⊗ S m) (E P)) (m + 1) (m + 1) (2 * m + 2) (by omega)
    ((cohPullback (fst (S m) (S m)) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega)))
    ((cohPullback (snd (S m) (S m)) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega)))
  exact he.trans (congrArg (fun a => CupAtDegree.cup (leftSpace m P) (2 * m + 2) m (3 * m + 2) (by omega) a
    ((cohPullback (snd (S m ⊗ S m) (E P)) m).hom (LocalNativeBallPrimitive.remainingClass m P v₀))) hp.symm)

theorem pairTop_pairing (m : ℕ) (P : Sphere (m + 1)) :
    (kroneckerMap (S m ⊗ S m) (2 * m + 2)).hom (pairTop m) (NativeDoubleFundamentalImage.spherePairClass m P) = 1 := by
  have he := CupAtDegreeCrossPairing.cross_cup_apply (S m) (S m) (m + 1) (m + 1) (2 * m + 2) (by omega)
    (SphereTopClass.topClass (m + 1) (by omega)) (SphereTopClass.topClass (m + 1) (by omega))
    (SphereUnitCandidate.fundamental (m + 1) (by omega)) (SphereUnitCandidate.fundamental (m + 1) (by omega))
  rw [SphereUnitCandidate.top_evaluation_one, one_mul] at he
  exact he

theorem remaining_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (E P) m).hom (LocalNativeBallPrimitive.remainingClass m P v₀)
      (MeridianEquatorHomology.fundamental m hm P) = 1 :=
  (congrArg (fun f => f (MeridianEquatorHomology.fundamental m hm P))
    (kroneckerMap_naturality_apply (ordinary P v₀) m (MeridianLoopClass.ordinaryTransgression m))).trans
      (MeridianPrimitiveNonzero.ordinary_pairing_one m hm P v₀)

theorem scalar_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (graphSpace P) (3 * m + 2)).hom
      (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀))
      (NativeDoubleFundamentalImage.fundamentalImage m hm P) = 1 := by
  have hn := CupAtDegreeCrossPairing.pairing_push (associator m P) (3 * m + 2)
    (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀))
    (NativeDoubleFundamentalImage.sphereTripleClass m hm P)
  have hc := CupAtDegreeCrossPairing.cross_cup_apply (S m ⊗ S m) (E P) (2 * m + 2) m (3 * m + 2) (by omega)
    (pairTop m) (LocalNativeBallPrimitive.remainingClass m P v₀)
    (NativeDoubleFundamentalImage.spherePairClass m P) (MeridianEquatorHomology.fundamental m hm P)
  have he := congrArg (fun a => (kroneckerMap (leftSpace m P) (3 * m + 2)).hom a
    (NativeDoubleFundamentalImage.sphereTripleClass m hm P)) (explicit_pullback m P v₀)
  exact hn.trans (he.trans (hc.trans (by rw [pairTop_pairing, remaining_pairing, one_mul])))

end
end Finsler.NativeGraphFundamentalScalar
