module

public import Finsler.Loop.NativeMatchingTransgression

/-! Fix the common meridian and cut phase in the NONADJACENT
matching family. The ORIGINAL tested loop detects the middle
meridian fundamental class with pairing1, for every such fixed
choice. This is a TESTED-FACTOR pairing, not the full Theta-cut
coefficient or a normalized Thom intersection multiplicity. -/
@[expose] public section
namespace Finsler.NativeMatchingTestedPairing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.MeridianLoopFamily Finsler.NativeMeridianMatchingLoci
open Finsler.NativeMatchingTransgression Finsler.NativeMatchingAdjacentFactors Finsler.NativeMatchingRetainedFactors
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

theorem constant_homology_zero (X Y : TopCat.{0}) (y : Y) (q : ℕ) (hq : q ≠ 0) :
    homologyPushZMod2 (TopCat.ofHom (ContinuousMap.const X y)) q = 0 := by
  let pt : TopCat.{0} := TopCat.of PUnit
  let a : X ⟶ pt := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let b : pt ⟶ Y := TopCat.ofHom (ContinuousMap.const PUnit y)
  have hf : TopCat.ofHom (ContinuousMap.const X y) = a ≫ b := by ext x : 1; rfl
  have hz : IsZero (homologyZMod2 pt q) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (C := ModuleCat.{0} (ZMod 2)) (n := q) coeff pt hq
  rw [hf]
  change ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).map (a ≫ b) = 0
  rw [Functor.map_comp]
  change homologyPushZMod2 a q ≫ homologyPushZMod2 b q = 0
  have ha : homologyPushZMod2 a q = 0 := hz.eq_of_tgt _ _
  rw [ha, zero_comp]

theorem constant_pullback_zero (X Y : TopCat.{0}) (y : Y) (q : ℕ) (hq : q ≠ 0)
    (a : cohomologyZMod2 Y q) :
    (cohPullback (TopCat.ofHom (ContinuousMap.const X y)) q).hom a = 0 := by
  apply kroneckerMap_injective X q
  rw [kroneckerMap_naturality_apply, constant_homology_zero X Y y q hq]
  simp only [ModuleCat.hom_zero, LinearMap.comp_zero, map_zero]

def middleSlice {n : ℕ} (P : Sphere n) (s : ClosedInterval) (v : equator P) :
    TopCat.of (equator P) ⟶ parameters P :=
  TopCat.ofHom ⟨fun w => (s, (v, w)), continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩

theorem middle_retained_constant {n : ℕ} (P : Sphere n) (v₀ : equator P) (s : ClosedInterval) (v : equator P) :
    middleSlice P s v ≫ retainedMap P v₀ 1 =
      TopCat.ofHom (ContinuousMap.const (equator P) (retainedMap P v₀ 1 (s, (v, v₀)))) := by
  ext w : 1
  exact nonadjacent_independent P v₀ v w v₀ s

theorem middle_remaining {n : ℕ} (P : Sphere n) (v₀ : equator P) (s : ClosedInterval) (v : equator P) :
    middleSlice P s v ≫ (remaining P v₀ ≫ BasedMeridianProducts.forget P) = ordinary P v₀ := by
  ext w : 1
  rfl

def tested (n : ℕ) (P : Sphere n) (v₀ : equator P) (s : ClosedInterval) (v : equator P) :
    TopCat.of (equator P) ⟶ ContinuousLoopModel.space n := middleSlice P s v ≫ testedMap P v₀ 1

theorem tested_pullback (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (s : ClosedInterval) (v : equator P) :
    (cohPullback (tested (m + 1) P v₀ s v) m).hom (MeridianLoopClass.ordinaryTransgression m) =
      (cohPullback (ordinary P v₀) m).hom (MeridianLoopClass.ordinaryTransgression m) := by
  have he := congrArg ((cohPullback (middleSlice P s v) m).hom)
    (original_tested_value P v₀ 1 m (SphereTopClass.topClass (m + 1) (by omega)))
  rw [map_add, ← pullback_comp, ← pullback_comp, ← pullback_comp, middle_remaining,
    middle_retained_constant] at he
  have hz := constant_pullback_zero (TopCat.of (equator P)) (ContinuousLoopModel.space (m + 1))
    (retainedMap P v₀ 1 (s, (v, v₀))) m (by omega) (MeridianLoopClass.ordinaryTransgression m)
  change (cohPullback (tested (m + 1) P v₀ s v) m).hom (MeridianLoopClass.ordinaryTransgression m) =
    (cohPullback (ordinary P v₀) m).hom (MeridianLoopClass.ordinaryTransgression m) +
      (cohPullback (TopCat.ofHom (ContinuousMap.const (equator P) (retainedMap P v₀ 1 (s, (v, v₀))))) m).hom
        (MeridianLoopClass.ordinaryTransgression m) at he
  rw [hz, add_zero] at he
  exact he

theorem tested_pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (s : ClosedInterval) (v : equator P) :
    (kroneckerMap (ContinuousLoopModel.space (m + 1)) m).hom (MeridianLoopClass.ordinaryTransgression m)
      ((homologyPushZMod2 (tested (m + 1) P v₀ s v) m).hom (MeridianEquatorHomology.fundamental m hm P)) = 1 := by
  have he := congrArg (fun a : cohomologyZMod2 (TopCat.of (equator P)) m =>
      (kroneckerMap (TopCat.of (equator P)) m).hom a (MeridianEquatorHomology.fundamental m hm P))
    (tested_pullback m hm P v₀ s v)
  rw [kroneckerMap_naturality_apply, kroneckerMap_naturality_apply] at he
  exact he.trans (MeridianPrimitiveNonzero.ordinary_pairing_one m hm P v₀)

theorem tested_homology_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (s : ClosedInterval) (v : equator P) :
    (homologyPushZMod2 (tested (m + 1) P v₀ s v) m).hom (MeridianEquatorHomology.fundamental m hm P) ≠ 0 := by
  intro hz
  have he := tested_pairing_one m hm P v₀ s v
  rw [hz, map_zero] at he
  exact zero_ne_one he

end
end Finsler.NativeMatchingTestedPairing
