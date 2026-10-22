module

public import Finsler.Loop.DiagonalComplementCut
public import Finsler.Loop.NativeMatchingTestedPairing

/-! BOTH actual ordered matching cuts are retained. Their ORIGINAL
tested-factor transgressions sum to the remaining primitive, for each
of the three unordered pairs. The paired slice detects a real nonzero
homology class with pairingONE. No Thom cap multiplicity or global
Theta-cut value is inferred from this factor calculation. -/
@[expose] public section
namespace Finsler.NativeComplementMatchingPairings
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.NativeMeridianMatchingLoci
open Finsler.NativeMatchingTransgression Finsler.NativeMatchingTestedPairing
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

def reverseDiagonal {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ DiagonalSelfCutRepresentatives.domain n :=
  intoDiagonal P v₀ b ≫ DiagonalComplementCut.complement n

def reverseTested {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ ContinuousLoopModel.space n := reverseDiagonal P v₀ b ≫ DiagonalSelfCutRepresentatives.tested n

def reverseRetained {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ ContinuousLoopModel.space n := reverseDiagonal P v₀ b ≫ DiagonalSelfCutRepresentatives.retained n

theorem reverse_tested_pullback {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (reverseTested P v₀ b) q).hom a =
      (cohPullback (NativeMatchingRetainedFactors.retainedMap P v₀ b) q).hom a := by
  change (cohPullback (intoDiagonal P v₀ b ≫
    (DiagonalComplementCut.complement n ≫ DiagonalSelfCutRepresentatives.tested n)) q).hom a = _
  rw [pullback_comp, DiagonalComplementCut.tested_cohomology_swap, ← pullback_comp]
  rfl

theorem reverse_retained_pullback {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (reverseRetained P v₀ b) q).hom a =
      (cohPullback (NativeMatchingAdjacentFactors.testedMap P v₀ b) q).hom a := by
  change (cohPullback (intoDiagonal P v₀ b ≫
    (DiagonalComplementCut.complement n ≫ DiagonalSelfCutRepresentatives.retained n)) q).hom a = _
  rw [pullback_comp, DiagonalComplementCut.retained_cohomology_swap, ← pullback_comp]
  rfl

theorem paired_tested_transgression {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (NativeMatchingAdjacentFactors.testedMap P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (reverseTested P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
        (cohPullback (remaining P v₀ ≫ BasedMeridianProducts.forget P) q).hom
          (ContinuousLoopSweep.transgression n q a) := by
  rw [reverse_tested_pullback]
  exact original_tested_retained_sum P v₀ b q a

def forwardSlice {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (s : ClosedInterval) (v : equator P) : TopCat.of (equator P) ⟶ ContinuousLoopModel.space n :=
  middleSlice P s v ≫ NativeMatchingAdjacentFactors.testedMap P v₀ b

def reverseSlice {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (s : ClosedInterval) (v : equator P) : TopCat.of (equator P) ⟶ ContinuousLoopModel.space n :=
  middleSlice P s v ≫ reverseTested P v₀ b

theorem paired_slice_pullback {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (s : ClosedInterval) (v : equator P) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (forwardSlice P v₀ b s v) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (reverseSlice P v₀ b s v) q).hom (ContinuousLoopSweep.transgression n q a) =
        (cohPullback (ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a) := by
  have he := congrArg ((cohPullback (middleSlice P s v) q).hom) (paired_tested_transgression P v₀ b q a)
  rw [map_add, ← pullback_comp, ← pullback_comp, ← pullback_comp, middle_remaining] at he
  exact he

def pairedClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    (s : ClosedInterval) (v : equator P) : homologyZMod2 (ContinuousLoopModel.space (m + 1)) m :=
  (homologyPushZMod2 (forwardSlice P v₀ b s v) m).hom (MeridianEquatorHomology.fundamental m hm P) +
    (homologyPushZMod2 (reverseSlice P v₀ b s v) m).hom (MeridianEquatorHomology.fundamental m hm P)

theorem paired_pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    (s : ClosedInterval) (v : equator P) :
    (kroneckerMap (ContinuousLoopModel.space (m + 1)) m).hom (MeridianLoopClass.ordinaryTransgression m)
      (pairedClass m hm P v₀ b s v) = 1 := by
  have he := congrArg (fun a : cohomologyZMod2 (TopCat.of (equator P)) m =>
    (kroneckerMap (TopCat.of (equator P)) m).hom a (MeridianEquatorHomology.fundamental m hm P))
    (paired_slice_pullback P v₀ b s v m (SphereTopClass.topClass (m + 1) (by omega)))
  rw [map_add] at he
  rw [kroneckerMap_naturality_apply, kroneckerMap_naturality_apply, kroneckerMap_naturality_apply] at he
  unfold pairedClass
  rw [map_add]
  exact he.trans (MeridianPrimitiveNonzero.ordinary_pairing_one m hm P v₀)

theorem pairedClass_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3)
    (s : ClosedInterval) (v : equator P) : pairedClass m hm P v₀ b s v ≠ 0 := by
  intro hz
  have he := paired_pairing_one m hm P v₀ b s v
  rw [hz, map_zero] at he
  exact zero_ne_one he

end
end Finsler.NativeComplementMatchingPairings
