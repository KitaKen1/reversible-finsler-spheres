module

public import Finsler.Loop.NativeGHPowerFiniteDetection
public import Finsler.Loop.CanonicalGHLengthSupport
public import Finsler.Topology.SmallLevel

/-! A genuine positive primitive support scale follows from the
ACTUAL small-energy deformation to constants and the ACTUAL length/
energy normalization homotopy. Genuine GH support addition then
makes the actual powers vanish up to a POSITIVE LINEAR length bound.
This is not the full ordinary HR detection-band theorem or full UF. -/
@[expose] public section
namespace Finsler.NativeGHPowerPositiveSupport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.RegularInterval Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

def constantsRetraction {n : ℕ} (F : ReversibleMetric n) {b : ℝ}
    (D : LevelDeformation F 0 b b) : TopCat.of (lev F b) ⟶ TopCat.of (consts n) :=
  TopCat.ofHom ⟨fun u => ⟨(D.r u).val,
    SmallLevel.lev_subset_consts F le_rfl (D.r_mem u u.property)⟩,
    (continuous_subtype_val.comp D.r.continuous).subtype_mk _⟩

def constantsHomotopy {n : ℕ} (F : ReversibleMetric n) {b : ℝ}
    (D : LevelDeformation F 0 b b) :
    TopCat.Homotopy (SupportedCap.subspaceMap (Loops n) (lev F b))
      (constantsRetraction F D ≫ SupportedCap.subspaceMap (Loops n) (consts n)) where
  toFun z := (D.H z).val
  continuous_toFun := continuous_subtype_val.comp D.H.continuous
  map_zero_left u := congrArg Subtype.val (D.H.map_zero_left u)
  map_one_left u := congrArg Subtype.val (D.H.map_one_left u)

theorem energy_restriction_zero {n : ℕ} (F : ReversibleMetric n) {b : ℝ}
    (D : LevelDeformation F 0 b b) (k : ℕ) (a : cohomologyZMod2 (Loops n) k)
    (ha : (cohPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k).hom a = 0) :
    (cohPullback (SupportedCap.subspaceMap (Loops n) (lev F b)) k).hom a = 0 := by
  have he := DiagonalCohomology.homotopy_pullback (constantsHomotopy F D) k a
  rw [Cup.pullback_comp, ha, map_zero] at he
  exact he

theorem exists_positive_length_zero {n : ℕ} (F : ReversibleMetric n)
    (k : ℕ) (a : cohomologyZMod2 (Loops n) k)
    (ha : (cohPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k).hom a = 0) :
    ∃ b : ℝ, 0 < b ∧ (cohPullback (LengthFilteredLoopRotation.full F b) k).hom a = 0 := by
  obtain ⟨b, hb, h⟩ := SmallLevel.exists_small_deformation F
  obtain ⟨D⟩ := h b hb le_rfl
  have hz := energy_restriction_zero F D k a ha
  have hf := congrArg (fun f : lengthSpace F b ⟶ Loops n => (cohPullback f k).hom a)
    (StrictLengthEnergyBridge.toEnergy_source F b)
  rw [Cup.pullback_comp, Cup.pullback_comp, hz, map_zero,
    LengthEnergyMaps.normalizer_cohomology] at hf
  exact ⟨b, hb, hf.symm⟩

theorem exists_primitive_support (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) :
    ∃ L : ℝ, 0 < L ∧ (cohPullback (LengthFilteredLoopRotation.full F L) m).hom
      (MeridianLoopClass.H1TransgressionClass m) = 0 :=
  exists_positive_length_zero F m (MeridianLoopClass.H1TransgressionClass m)
    (NativeGHPowerLengthDetection.power_restriction_zero m hm 0)

theorem exists_linear_power_zero (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ r : ℕ,
      (cohPullback (LengthFilteredLoopRotation.full F (((r : ℝ) + 1) * ℓ))
        (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 := by
  obtain ⟨L, hL, hω⟩ := exists_primitive_support m hm F
  let ℓ := L / 2
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith
  refine ⟨ℓ, hℓ, ?_⟩
  intro r
  induction r with
  | zero =>
    exact CanonicalGHLengthSupport.restriction_zero_mono F m
      (MeridianLoopClass.H1TransgressionClass m)
      (by norm_num; dsimp [ℓ]; linarith : (((0 : ℕ) : ℝ) + 1) * ℓ ≤ L) hω
  | succ r ih =>
    have hlt : ((((r + 1 : ℕ) : ℝ) + 1) * ℓ) < L + ((r : ℝ) + 1) * ℓ := by
      push_cast
      dsimp [ℓ]
      nlinarith
    exact CanonicalGHLengthSupport.product_restriction_zero (by omega) F m
      (NativeGHPowers.degree m r) (MeridianLoopClass.H1TransgressionClass m)
      (NativeGHPowers.power m r) hω ih hlt

theorem exists_detector_length_lower (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ (r : ℕ) (R : ℝ)
      (z : homologyZMod2 (lengthSpace F R) (NativeGHPowers.degree m r)),
      (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
        ((homologyPushZMod2 (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom z) ≠ 0 →
      ((r : ℝ) + 1) * ℓ < R := by
  obtain ⟨ℓ, hℓ, h⟩ := exists_linear_power_zero m hm F
  refine ⟨ℓ, hℓ, ?_⟩
  intro r R z hpair
  by_contra hR
  have hz := CanonicalGHLengthSupport.restriction_zero_mono F (NativeGHPowers.degree m r)
    (NativeGHPowers.power m r) (le_of_not_gt hR) (h r)
  have hn := congrArg (fun φ : homologyDualZMod2 (lengthSpace F R) (NativeGHPowers.degree m r) => φ z)
    (kroneckerMap_naturality_apply (LengthFilteredLoopRotation.full F R)
      (NativeGHPowers.degree m r) (NativeGHPowers.power m r))
  change (kroneckerMap (lengthSpace F R) (NativeGHPowers.degree m r)).hom
      ((cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom
        (NativeGHPowers.power m r)) z =
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom z) at hn
  rw [hz, map_zero, LinearMap.zero_apply] at hn
  exact hpair hn.symm

end
end Finsler.NativeGHPowerPositiveSupport
