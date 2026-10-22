module

public import Finsler.Loop.NativeHighPowerUnit
public import Finsler.Loop.CanonicalGHLengthSupport
public import Finsler.Loop.CanonicalGlobalSelfCutFiltered

/-! The ORIGINAL filtered single cut of every SAME Theta power, with any
actual GH support length L. Its output lies below a-L+3ε and has the
original absolute UNIT as full image. This works for EVERY filtered lift
of that same full power; no injectivity of a fixed length cut is assumed. -/
@[expose] public section
namespace Finsler.NativeHighPowerFilteredCut
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable (m : ℕ) (F : ReversibleMetric (m + 1)) (r : ℕ) {a L ε : ℝ}

variable (hL : (cohPullback (LengthFilteredLoopRotation.full F L)
  (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0)

def supportedCochain := NormalizedRelativeRepresentative.raw (Loops (m + 1))
  (SelfCutOscillation.short F L) (NativeGHPowers.degree m r) (NativeGHPowers.power m r) hL

theorem supported_closed : cochainCoboundary (ZMod 2) (Loops (m + 1))
    (NativeGHPowers.degree m r) (supportedCochain m F r hL) = 0 :=
  NormalizedRelativeRepresentative.raw_closed _ _ _ _ hL

theorem supported_zero : cochainPullback (LengthFilteredLoopRotation.full F L)
    (NativeGHPowers.degree m r) (supportedCochain m F r hL) = 0 :=
  NormalizedRelativeRepresentative.raw_supported _ _ _ _ hL

theorem supported_class : cocycleClass (Loops (m + 1)) (NativeGHPowers.degree m r)
    (supportedCochain m F r hL) (supported_closed m F r hL) = NativeGHPowers.power m r :=
  NormalizedRelativeRepresentative.raw_class _ _ _ _ hL

def aligned {X : TopCat.{0}} (z : homologyZMod2 X (NativeThetaPowers.degree m r)) :
    homologyZMod2 X ((m + NativeGHPowers.degree m r) + (m + 1)) :=
  (eqToHom (congrArg (homologyZMod2 X) (NativeHighPowerUnitComparison.degree_match m r))).hom z

theorem aligned_push {X Y : TopCat.{0}} (f : X ⟶ Y)
    (z : homologyZMod2 X (NativeThetaPowers.degree m r)) :
    (homologyPushZMod2 f ((m + NativeGHPowers.degree m r) + (m + 1))).hom (aligned m r z) =
      aligned m r ((homologyPushZMod2 f (NativeThetaPowers.degree m r)).hom z) := by
  have hc {i j : ℕ} (h : i = j) (w : homologyZMod2 X i) :
      (homologyPushZMod2 f j).hom ((eqToHom (congrArg (homologyZMod2 X) h)).hom w) =
        (eqToHom (congrArg (homologyZMod2 Y) h)).hom ((homologyPushZMod2 f i).hom w) := by
    subst j
    rfl
  exact hc (NativeHighPowerUnitComparison.degree_match m r) z

def cut (hε : 0 < ε) (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r)) :
    homologyZMod2 (lengthSpace F (a - L + 3 * ε)) (m + 1) :=
  ((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε
    (supportedCochain m F r hL) (supported_closed m F r hL) (supported_zero m F r hL)
    (a := a)).homology (m + 1)).hom (aligned m r z)

variable (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
variable (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r))
variable (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
  (NativeThetaPowers.degree m r)).hom z = NativeThetaPowers.fullPower m hm F P v₀ r)

include hL hz

theorem cut_full (hε : 0 < ε) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a - L + 3 * ε)) (m + 1)).hom
      (cut m F r hL hε z) = NativeHighPowerUnitComparison.singleCut m hm F P v₀ r := by
  have h := CanonicalGlobalSelfCutFiltered.original_filtered m (by omega)
    (NativeGHPowers.degree m r) F hε (supportedCochain m F r hL)
    (supported_closed m F r hL) (supported_zero m F r hL) (m + 1) (aligned m r z)
  rw [supported_class, aligned_push] at h
  change (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a - L + 3 * ε)) (m + 1)).hom
    (cut m F r hL hε z) =
    (CanonicalGlobalSelfCut.map m (NativeGHPowers.degree m r) (m + 1) (NativeGHPowers.power m r)).hom
      (aligned m r ((homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
        (NativeThetaPowers.degree m r)).hom z)) at h
  rw [hz] at h
  exact h

theorem cut_UNIT (hε : 0 < ε) :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (a - L + 3 * ε)) (m + 1)).hom
        (cut m F r hL hε z)) = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  rw [cut_full m F r hL hm P v₀ z hz hε]
  exact NativeHighPowerUnit.single_UNIT m hm F P v₀ r

theorem cut_pairing_one (hε : 0 < ε) :
    (kroneckerMap (Loops (m + 1)) (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m)
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (a - L + 3 * ε)) (m + 1)).hom
        (cut m F r hL hε z)) = 1 := by
  rw [cut_full m F r hL hm P v₀ z hz hε,
    NativeHighPowerUnitComparison.single_cut_pairing]
  exact NativeHighPowerUnit.scalar_one m hm F P v₀ r

theorem cut_ne_zero (hε : 0 < ε) : cut m F r hL hε z ≠ 0 := by
  intro hzero
  have h := cut_pairing_one m F r hL hm P v₀ z hz hε
  rw [hzero, map_zero, map_zero] at h
  exact zero_ne_one h

theorem output_positive (hε : 0 < ε) : 0 < a - L + 3 * ε := by
  by_contra hpos
  let b := a - L + 3 * ε
  have : IsEmpty (SelfCutOscillation.short F b) := short_empty F b (le_of_not_gt hpos)
  have hr : (cohPullback (LengthFilteredLoopRotation.full F b) (m + 1)).hom
      (MeridianThetaCutCoefficient.evaluationClass m) = 0 := by
    rw [← cocycleClass_classRepr (Loops (m + 1)) (m + 1)
      (MeridianThetaCutCoefficient.evaluationClass m), cohPullback_cocycleClass]
    have he : cochainPullback (LengthFilteredLoopRotation.full F b) (m + 1)
        (classRepr (Loops (m + 1)) (m + 1) (MeridianThetaCutCoefficient.evaluationClass m)) = 0 :=
      (EmptySingularChains.chains_zero (lengthSpace F b) (m + 1)).eq_of_src _ _
    simp only [he, cocycleClass_zero]
  have hn := congrArg (fun φ : homologyDualZMod2 (lengthSpace F b) (m + 1) =>
    φ (cut m F r hL hε z))
    (kroneckerMap_naturality_apply (LengthFilteredLoopRotation.full F b) (m + 1)
      (MeridianThetaCutCoefficient.evaluationClass m))
  change (kroneckerMap (lengthSpace F b) (m + 1)).hom
    ((cohPullback (LengthFilteredLoopRotation.full F b) (m + 1)).hom
      (MeridianThetaCutCoefficient.evaluationClass m)) (cut m F r hL hε z) = _ at hn
  rw [hr, map_zero, LinearMap.zero_apply] at hn
  exact zero_ne_one (hn.trans (cut_pairing_one m F r hL hm P v₀ z hz hε))

theorem support_le_input : L ≤ a := by
  by_contra h
  have hε : 0 < (L - a) / 6 := by linarith
  have hp := output_positive m F r hL hm P v₀ z hz hε
  linarith

end
end Finsler.NativeHighPowerFilteredCut
