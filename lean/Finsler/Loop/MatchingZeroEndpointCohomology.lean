module

public import Finsler.Loop.MatchingEndpointEvaluation
public import Finsler.Loop.NativeBallDiagonalCohomology
public import Finsler.Topology.CrossCupPairing
public import Finsler.Loop.CupAtDegree
public import Finsler.Loop.MeridianPrimitiveNonzero

/-! Compute the actual time-zero matching factors on the real
equator product. Tested transgression is left plus right; retained
transgression is left. Their cup evaluates to ONE on the actual
fundamental cross. All clocks were compared by real pause homotopies. -/
@[expose] public section
namespace Finsler.MatchingZeroEndpointCohomology
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

abbrev E {n : ℕ} (P : Sphere n) := TopCat.of (equator P)

def meridianClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (cohPullback (ordinary P v₀) m).hom (MeridianLoopClass.ordinaryTransgression m)

def leftClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (cohPullback (fst (E P) (E P)) m).hom (meridianClass m P v₀)

def rightClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (cohPullback (snd (E P) (E P)) m).hom (meridianClass m P v₀)

def testedAt {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    MatchingRelativeOutputEndpointTrace.source P ⟶ Loops n :=
  DoubleRelativeTimeCylinder.atTime (MatchingRelativeOutputEndpointTrace.source P) 0 ≫
    MatchingOriginalRelativeOutputSplit.testedH1 P v₀ 1

theorem tested_ordinary {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    testedAt P v₀ ≫ ContinuousLoopModel.inclusion n = MatchingZeroEndpointRepresentatives.tested P v₀ := by
  ext z : 1
  rfl

theorem retained_ordinary {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    MatchingEndpointEvaluation.retainedAt P v₀ 0 ≫ ContinuousLoopModel.inclusion n =
      fst (E P) (E P) ≫ MatchingZeroEndpointRepresentatives.retained P v₀ := by
  ext z : 1
  exact NativeMatchingRetainedFactors.nonadjacent_independent P v₀ z.1 z.2 v₀ 0

theorem H1_transgression (m : ℕ) :
    MeridianLoopClass.H1TransgressionClass m =
      (cohPullback (ContinuousLoopModel.inclusion (m + 1)) m).hom (MeridianLoopClass.ordinaryTransgression m) := rfl

theorem double_transgression (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (BasedMeridianProducts.doubleFamily P v₀ ≫ BasedMeridianProducts.forget P) m).hom
      (MeridianLoopClass.ordinaryTransgression m) = leftClass m P v₀ + rightClass m P v₀ := by
  let f := fst (E P) (E P) ≫ BasedMeridianProducts.family P v₀
  let g := snd (E P) (E P) ≫ BasedMeridianProducts.family P v₀
  have hd : BasedMeridianProducts.doubleFamily P v₀ = NativeMatchingTransgression.concat f g := by
    ext z : 1
    rfl
  have hf : f ≫ BasedMeridianProducts.forget P = fst (E P) (E P) ≫ ordinary P v₀ := by ext z : 1; rfl
  have hg : g ≫ BasedMeridianProducts.forget P = snd (E P) (E P) ≫ ordinary P v₀ := by ext z : 1; rfl
  rw [hd]
  change (cohPullback (NativeMatchingTransgression.concat f g ≫ BasedMeridianProducts.forget P) m).hom
    (ContinuousLoopSweep.transgression (m + 1) m _) = _
  rw [NativeMatchingTransgression.concat_transgression, hf, hg, Cup.pullback_comp, Cup.pullback_comp]
  rfl

theorem tested_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (testedAt P v₀) m).hom (MeridianLoopClass.H1TransgressionClass m) =
      leftClass m P v₀ + rightClass m P v₀ := by
  rw [H1_transgression, ← Cup.pullback_comp, tested_ordinary,
    MatchingZeroEndpointRepresentatives.tested_cohomology, double_transgression]

theorem retained_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    (cohPullback (MatchingEndpointEvaluation.retainedAt P v₀ 0) m).hom (MeridianLoopClass.H1TransgressionClass m) =
      leftClass m P v₀ := by
  rw [H1_transgression, ← Cup.pullback_comp, retained_ordinary, Cup.pullback_comp,
    MatchingZeroEndpointRepresentatives.retained_cohomology]
  rfl

theorem left_square_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    cupZMod2 (leftClass m P v₀) (leftClass m P v₀) = 0 := by
  have hn := Cup.naturality (fst (E P) (E P)) m m (meridianClass m P v₀) (meridianClass m P v₀)
  exact hn.symm.trans ((congrArg (cohPullback (fst (E P) (E P)) (m + m)).hom
    (NativeBallDiagonalCohomology.equator_cohomology_zero m (m + m) P (by omega) (by omega) _)).trans (map_zero _))

theorem cup_reduction (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    cupZMod2 (leftClass m P v₀ + rightClass m P v₀) (leftClass m P v₀) =
      cupZMod2 (leftClass m P v₀) (rightClass m P v₀) := by
  have ha := CupAtDegree.add_left (E P ⊗ E P) m m (m + m) rfl
    (leftClass m P v₀) (rightClass m P v₀) (leftClass m P v₀)
  change cupZMod2 _ _ = cupZMod2 _ _ + cupZMod2 _ _ at ha
  rw [ha, left_square_zero m hm, zero_add]
  exact CupAtDegree.comm (E P ⊗ E P) m m (m + m) rfl _ _

def sourceClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) : homologyZMod2 (E P ⊗ E P) (m + m) :=
  FilteredBilinearLoopProduct.cross (E P) (E P) m m (m + m) rfl
    (MeridianEquatorHomology.fundamental m hm P) (MeridianEquatorHomology.fundamental m hm P)

theorem meridian_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (E P) m).hom (meridianClass m P v₀) (MeridianEquatorHomology.fundamental m hm P) = 1 :=
  (congrArg (fun f => f (MeridianEquatorHomology.fundamental m hm P))
    (kroneckerMap_naturality_apply (ordinary P v₀) m (MeridianLoopClass.ordinaryTransgression m))).trans
      (MeridianPrimitiveNonzero.ordinary_pairing_one m hm P v₀)

theorem pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (E P ⊗ E P) (m + m)).hom
      (cupZMod2 (leftClass m P v₀ + rightClass m P v₀) (leftClass m P v₀)) (sourceClass m hm P) = 1 := by
  rw [cup_reduction m hm]
  have he := CrossCupPairing.cross_cup_apply (E P) (E P) m m (meridianClass m P v₀) (meridianClass m P v₀)
    (MeridianEquatorHomology.fundamental m hm P) (MeridianEquatorHomology.fundamental m hm P)
  rw [meridian_pairing, one_mul] at he
  exact he

end
end Finsler.MatchingZeroEndpointCohomology
