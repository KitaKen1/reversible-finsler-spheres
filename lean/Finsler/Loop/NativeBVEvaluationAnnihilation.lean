module

public import Finsler.Loop.NativeOrdinaryGHCupVanishing
public import Finsler.Topology.SpherePuncturedEvaluation

/-! Kill the ENTIRE evaluation-cup second term in every n>=3. In a
positive multiple of m, actual free-loop homology comes from a punctured
evaluation patch; evaluation vanishes on that patch. No vanishing of
the bare factor's rotation is needed, including the exceptional m=2. -/
@[expose] public section
namespace Finsler.NativeBVEvaluationAnnihilation
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily Finsler.H1PuncturedRelativeChart
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private theorem cast_zero (X : TopCat.{0}) {i j : ℕ} (h : i = j) : CupUnit.absoluteCast X h 0 = 0 := by
  subst j
  rfl

private theorem cup_class (X : TopCat.{0}) (p q N : ℕ) (hN : p + q = N)
    (A : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q)
    (hA : cochainCoboundary (ZMod 2) X p A = 0) (hB : cochainCoboundary (ZMod 2) X q B = 0) :
    cocycleClass X N (CupOne.cup X p q N hN A B) (CupCapOrder.closed _ _ _ _ _ _ _ hA hB) =
      CupAtDegree.cup X p q N hN (cocycleClass X p A hA) (cocycleClass X q B hB) := by
  subst N
  simpa only [CupOne.cup_comparison, CupAtDegree.cup, CupAtDegree.cast_self] using (cupZMod2_mk A hA B hB).symm

def patchMap {n : ℕ} (P : Sphere n) : TopCat.of (fullDomain P) ⟶ Loops n :=
  TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain P)) ≫ FullLoopModel.forget n

theorem patch_evaluation_zero (m : ℕ) (P : Sphere (m + 1)) :
    (cohPullback (patchMap P) (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m) = 0 := by
  unfold MeridianThetaCutCoefficient.evaluationClass
  rw [← Cup.pullback_comp]
  apply SpherePuncturedEvaluation.evaluation_topClass_zero (m + 1) (by omega) (antipode P)
  intro x
  exact x.property

theorem patch_surjective (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    Function.Surjective (homologyPushZMod2 (patchMap (antipode P)) ((k + 1) * m)).hom := by
  intro z
  obtain ⟨w, hw⟩ := (NativeUnitEvaluationKernelRoute.fullHomology (m + 1) ((k + 1) * m)).surjective z
  obtain ⟨u, hu⟩ := NativeEvaluationPatchGeneration.south_generates P v₀ ((k + 1) * m)
    (NativeGHCoverSurjectivity.fromPatches_surjective m hm P v₀ k) w
  refine ⟨u, ?_⟩
  rw [patchMap, ← SplitPairHomologyKernel.push_comp_apply, hu]
  exact hw

theorem evaluation_cup_zero (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (q N k : ℕ) (hN : (m + 1) + q = N) (hD : N = (k + 1) * m)
    (b : cohomologyZMod2 (Loops (m + 1)) q) :
    CupAtDegree.cup (Loops (m + 1)) (m + 1) q N hN (MeridianThetaCutCoefficient.evaluationClass m) b = 0 := by
  have hs : Function.Surjective (homologyPushZMod2 (patchMap (antipode P)) N).hom := by
    rw [hD]
    exact patch_surjective m hm P v₀ k
  apply CupSquareZeroTransport.pullback_injective (patchMap (antipode P)) N hs
  rw [map_zero, CupAtDegree.naturality, patch_evaluation_zero]
  unfold CupAtDegree.cup
  rw [Cup.zero_cup]
  exact cast_zero _ _

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)
  (P : Sphere (m + 1)) (v₀ : equator P)

include P v₀ in
theorem secondTerm_class_zero : cocycleClass _ _ (NativeBVOrdinaryCupRotation.secondTerm m hm F r)
    (NativeBVOrdinaryCupRotation.secondTerm_closed m hm F r) = 0 := by
  have hc : cocycleClass _ _ (NativeBVOrdinaryCupRotation.secondTerm m hm F r)
      (NativeBVOrdinaryCupRotation.secondTerm_closed m hm F r) =
      CupAtDegree.cup (Loops (m + 1)) (m + 1) (NativeBVOrdinaryCupRotation.bareDegree m r - 1)
        (NativeGHPowers.degree m (r + 1))
        (by rw [NativeNearCutPowerSubstitution.degree_match]; dsimp [NativeBVOrdinaryCupRotation.bareDegree]; omega)
        (MeridianThetaCutCoefficient.evaluationClass m)
        (cocycleClass _ _ (NativeBVOrdinaryCupRotation.bareRotation m hm F r)
          (NativeBVOrdinaryCupRotation.bareRotation_closed m hm F r)) := by
    have h := cup_class (Loops (m + 1)) (m + 1) (NativeBVOrdinaryCupRotation.bareDegree m r - 1)
      (NativeGHPowers.degree m (r + 1))
      (by rw [NativeNearCutPowerSubstitution.degree_match]; dsimp [NativeBVOrdinaryCupRotation.bareDegree]; omega)
      (NativeBVNormalizedSource.evaluation m) (NativeBVOrdinaryCupRotation.bareRotation m hm F r)
      (NativeBVNormalizedSource.evaluation_closed m) (NativeBVOrdinaryCupRotation.bareRotation_closed m hm F r)
    rw [NativeBVNormalizedSource.evaluation_class] at h
    exact h
  exact hc.trans (evaluation_cup_zero m hm P v₀ _ _ (2 * r + 2) _
    (by rw [NativeGHPowers.degree_formula]; ring) _)

include P v₀ in
theorem secondTerm_cycles_zero : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
    NativeBVOrdinaryCupRotation.secondTerm m hm F r = 0 := by
  apply ConcreteCategory.hom_ext
  intro c
  have he := congrArg (fun a => (kroneckerMap _ (NativeGHPowers.degree m (r + 1))).hom a
    (((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c))
      (secondTerm_class_zero m hm F r P v₀)
  rw [kroneckerMap_cocycleClass, map_zero, LinearMap.zero_apply] at he
  exact (kroneckerFunctional_apply _ _ _ (NativeBVOrdinaryCupRotation.secondTerm_closed m hm F r) c).symm.trans he

end
end Finsler.NativeBVEvaluationAnnihilation
