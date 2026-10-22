module

public import Finsler.Loop.NativePrimitiveBVComparison

/-! Concrete high-degree BV inputs: start with the SAME original triple
meridian cube and repeatedly use the EXISTING strict-length Theta product.
Their original GH pairing is ONE. Their higher BV images are not yet asserted nonzero. -/
@[expose] public section
namespace Finsler.NativeRaisedBVCandidates
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

private theorem push_cast {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (z : homologyZMod2 X i) :
    (homologyPushZMod2 f j).hom ((eqToHom (congrArg (homologyZMod2 X) h)).hom z) =
      (eqToHom (congrArg (homologyZMod2 Y) h)).hom ((homologyPushZMod2 f i).hom z) := by
  subst j
  rfl

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def filtered : (r : ℕ) → homologyZMod2 (lengthSpace F (NativeThetaPowers.bound m F P v₀ r))
    (NativeGHPowers.degree m (r + 1))
  | 0 => (eqToHom (congrArg (homologyZMod2 (lengthSpace F (NativeThetaLengthCut.bound F P v₀)))
      (NativePrimitiveBVComparison.cube_degree m))).hom (NativeThetaLengthCut.cube m (by omega) F P v₀)
  | r + 1 => NativePrimitiveCutSurjective.raised m hm F P v₀ (NativeThetaPowers.bound m F P v₀ r)
      (by norm_num : (0 : ℝ) < 1) (NativeGHPowers.degree m (r + 1)) (filtered r)

def full (r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  (homologyPushZMod2 (LengthFilteredLoopRotation.full F (NativeThetaPowers.bound m F P v₀ r))
    (NativeGHPowers.degree m (r + 1))).hom (filtered m hm F P v₀ r)

theorem full_zero : full m hm F P v₀ 0 = NativePrimitiveBVComparison.cube m hm P v₀ := by
  unfold full filtered
  dsimp only [NativeThetaPowers.bound]
  rw [push_cast _ (NativePrimitiveBVComparison.cube_degree m)]
  apply congrArg (eqToHom (congrArg (homologyZMod2 (Loops (m + 1)))
    (NativePrimitiveBVComparison.cube_degree m))).hom
  have hc := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (3 * m)).obj coeff).map_comp
      (NativeThetaLengthCut.family F P v₀)
      (LengthFilteredLoopRotation.full F (NativeThetaLengthCut.bound F P v₀)))
        (BasedMeridianProducts.tripleSource m (by omega) P)
  rw [NativeThetaLengthCut.family_full] at hc
  exact hc.symm.trans (NativeH1TripleMeridian.cube_original m (by omega) P v₀)

theorem full_succ_cut (r : ℕ) :
    (CanonicalGlobalSelfCut.map m m (NativeGHPowers.degree m (r + 1))
      (MeridianLoopClass.H1TransgressionClass m)).hom (full m hm F P v₀ (r + 1)) = full m hm F P v₀ r :=
  NativePrimitiveCutSurjective.raised_cut_full m hm F P v₀ (NativeThetaPowers.bound m F P v₀ r)
    (NativeThetaPowers.bound_positive m F P v₀ r) (by norm_num : (0 : ℝ) < 1)
    (NativeGHPowers.degree m (r + 1)) (filtered m hm F P v₀ r)

theorem pairing_one (r : ℕ) :
    (kroneckerMap _ (NativeGHPowers.degree m (r + 1))).hom (NativeGHPowers.power m (r + 1))
      (full m hm F P v₀ r) = 1 := by
  induction r with
  | zero => rw [full_zero]; exact NativePrimitiveBVComparison.cube_pairing_one m hm P v₀
  | succ r ih =>
    have h := CanonicalGlobalSelfCut.pairing m m (NativeGHPowers.degree m (r + 1))
      (MeridianLoopClass.H1TransgressionClass m) (NativeGHPowers.power m (r + 1))
      (full m hm F P v₀ (r + 1))
    rw [full_succ_cut] at h
    exact h.symm.trans ih

theorem full_eq_detector (r : ℕ) : full m hm F P v₀ r = NativeGHRankOne.detector m hm P v₀ (r + 1) :=
  NativeGHRankOne.pairing_injective m hm P v₀ (r + 1)
    ((pairing_one m hm F P v₀ r).trans (NativeGHRankOne.detector_pairing m hm P v₀ (r + 1)).symm)

theorem full_ne_zero (r : ℕ) : full m hm F P v₀ r ≠ 0 := by
  intro h
  have hp := pairing_one m hm F P v₀ r
  rw [h, map_zero] at hp
  exact zero_ne_one hp

theorem filtered_ne_zero (r : ℕ) : filtered m hm F P v₀ r ≠ 0 := by
  intro h
  apply full_ne_zero m hm F P v₀ r
  unfold full
  rw [h, map_zero]

theorem full_independent (G : ReversibleMetric (m + 1)) (Q : Sphere (m + 1)) (w₀ : equator Q) (r : ℕ) :
    full m hm G Q w₀ r = full m hm F P v₀ r :=
  NativeGHRankOne.pairing_injective m hm P v₀ (r + 1)
    ((pairing_one m hm G Q w₀ r).trans (pairing_one m hm F P v₀ r).symm)

end
end Finsler.NativeRaisedBVCandidates
