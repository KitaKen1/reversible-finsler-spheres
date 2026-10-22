module

public import Finsler.Loop.NativeGHCoverSurjectivity
public import Finsler.Loop.NativeEvaluationPatchGeneration
public import Finsler.Loop.NativeGHNearOptimalDetection

/-! Actual GH-degree homology is one-dimensional, and pairing with the
SAME original GH power is an actual linear equivalence to F2. -/
@[expose] public section
namespace Finsler.NativeGHRankOne
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily Finsler.H1PuncturedRelativeChart
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem full_finite_rank_le_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    Module.Finite (ZMod 2) (homologyZMod2 (fullPair (m + 1)).fst ((k + 1) * m)) ∧
      Module.finrank (ZMod 2) (homologyZMod2 (fullPair (m + 1)).fst ((k + 1) * m)) ≤ 1 := by
  let e := ((H1PuncturedPatchHomology.fullDomainHomologyIso (antipode P) ((k + 1) * m)).trans
    (H1BasedFiberTransport.homologyIso (antipode P) P ((k + 1) * m))).toLinearEquiv
  obtain ⟨f, hf⟩ := PathSphereRankTower.based_embedding m (by omega) P v₀ (k + 1)
  have hi : Function.Injective (f.comp e.toLinearMap) := hf.comp e.injective
  have := Module.Finite.of_injective (f.comp e.toLinearMap) hi
  have hdim := (LinearMap.finrank_le_finrank_of_injective hi).trans_eq (Module.finrank_self (ZMod 2))
  let j := (homologyPushZMod2
    (TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain (antipode P)))) ((k + 1) * m)).hom
  have hj : Function.Surjective j := NativeEvaluationPatchGeneration.south_generates P v₀ ((k + 1) * m)
    (NativeGHCoverSurjectivity.fromPatches_surjective m hm P v₀ k)
  have := Module.Finite.of_surjective j hj
  exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_surjective hj).trans hdim⟩

theorem gh_finite_rank_le_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    Module.Finite (ZMod 2) (homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r)) ∧
      Module.finrank (ZMod 2) (homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r)) ≤ 1 := by
  rw [NativeGHPowers.degree_formula]
  obtain ⟨hfin, hdim⟩ := full_finite_rank_le_one m hm P v₀ (2 * r)
  have := hfin
  let e := NativeUnitEvaluationKernelRoute.fullHomology (m + 1) ((2 * r + 1) * m)
  have := Module.Finite.equiv e
  exact ⟨inferInstance, e.finrank_eq.symm.trans_le hdim⟩

theorem gh_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    Module.finrank (ZMod 2) (homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r)) = 1 := by
  obtain ⟨hfin, hle⟩ := gh_finite_rank_le_one m hm P v₀ r
  have := hfin
  obtain ⟨z, hz⟩ := NativeGHNearOptimalDetection.exists_pairing_one _ _ (NativeGHPowers.power m r)
    (NativeGHPowers.power_ne_zero m hm (roundMetric (m + 1)) P v₀ r)
  have hn : z ≠ 0 := by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
  have hp := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mpr ⟨z, hn⟩
  omega

theorem pairing_injective (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    Function.Injective ((kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)) := by
  let f := (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
  obtain ⟨z, hz⟩ := NativeGHNearOptimalDetection.exists_pairing_one _ _ (NativeGHPowers.power m r)
    (NativeGHPowers.power_ne_zero m hm (roundMetric (m + 1)) P v₀ r)
  have hn : z ≠ 0 := by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
  intro a b hab
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (gh_finrank_one m hm P v₀ r) hn (a - b)
  have he := congrArg f hc
  change f (c • z) = f (a - b) at he
  rw [map_smul, map_sub, hab, sub_self] at he
  change c * f z = 0 at he
  rw [show f z = 1 from hz, mul_one] at he
  rw [he, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

def pairingEquiv (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r) ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofBijective ((kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r))
    ⟨pairing_injective m hm P v₀ r, by
      obtain ⟨z, hz⟩ := NativeGHNearOptimalDetection.exists_pairing_one _ _ (NativeGHPowers.power m r)
        (NativeGHPowers.power_ne_zero m hm (roundMetric (m + 1)) P v₀ r)
      intro c
      refine ⟨c • z, ?_⟩
      rw [map_smul, hz]
      exact mul_one c⟩

def detector (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r) := (pairingEquiv m hm P v₀ r).symm 1

theorem detector_pairing (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
      (detector m hm P v₀ r) = 1 := (pairingEquiv m hm P v₀ r).apply_symm_apply 1

theorem nonzero_iff_pairing_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r)) :
    z ≠ 0 ↔ (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) z = 1 := by
  let f := (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
  constructor
  · intro hz
    have hf : f z ≠ 0 := fun h => hz (pairing_injective m hm P v₀ r (h.trans (map_zero f).symm))
    have hc : f z = 0 ∨ f z = 1 := by generalize f z = c; fin_cases c <;> simp
    exact hc.resolve_left hf
  · intro hz h
    rw [h, map_zero] at hz
    exact zero_ne_one hz

theorem nonzero_eq_detector (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m r)) (hz : z ≠ 0) :
    z = detector m hm P v₀ r :=
  pairing_injective m hm P v₀ r ((nonzero_iff_pairing_one m hm P v₀ r z).mp hz |>.trans
    (detector_pairing m hm P v₀ r).symm)

end
end Finsler.NativeGHRankOne
