module

public import Finsler.Loop.NativeConstantUnitFromPathMV

/-! The actual degree-n full/H1/ordinary free-loop homology is
one-dimensional for n>=3. The equivalences retain actual evaluation
as the full-model forward map and the actual constant section gives
the inverse. This computes only this degree, not the full loop ring. -/
@[expose] public section
namespace Finsler.NativeDegreeNLoopHomology
open CategoryTheory AlgebraicTopology SphereOddDegree
open CategoryTheory.Limits
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem based_top_zero (m : ℕ) (hm : 2 ≤ m)
    (P : Sphere (m + 1)) (v₀ : equator P) :
    IsZero (homologyZMod2 (TopCat.of (H1LocalFiber.based P)) (m + 1)) :=
  NativeEvaluationOrdinaryBasedGap.based_zero_of_path_zero P (m + 1)
    (PathSphereHomologyGap.path_top_zero m hm P P v₀)

theorem evaluation_surjective (n k : ℕ) : Function.Surjective (homologyPushZMod2 (fullEval n) k).hom := by
  intro z
  refine ⟨(homologyPushZMod2 (SphereTopClass.fullSection n) k).hom z, ?_⟩
  rw [SplitPairHomologyKernel.push_comp_apply, SphereTopClass.fullSection_eval,
    SplitPairHomologyKernel.push_id_apply]

def evaluationEquiv (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (fullPair (m + 1)).fst (m + 1) ≃ₗ[ZMod 2]
      homologyZMod2 (sphere (m + 1)) (m + 1) :=
  LinearEquiv.ofBijective (homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom
    ⟨NativeConstantUnitFromPathMV.full_evaluation_injective m hm P v₀, evaluation_surjective _ _⟩

theorem evaluationEquiv_apply (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (z : homologyZMod2 (fullPair (m + 1)).fst (m + 1)) :
    evaluationEquiv m hm P v₀ z = (homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom z := rfl

def fullScalarEquiv (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (fullPair (m + 1)).fst (m + 1) ≃ₗ[ZMod 2] ZMod 2 :=
  (evaluationEquiv m hm P v₀).trans (SphereTopClass.homologyEquiv (m + 1) (by omega))

def h1ScalarEquiv (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) (m + 1) ≃ₗ[ZMod 2] ZMod 2 :=
  (NativeUnitEvaluationKernelRoute.fullHomology (m + 1) (m + 1)).symm.trans (fullScalarEquiv m hm P v₀)

def ordinaryScalarEquiv (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (ContinuousLoopModel.space (m + 1)) (m + 1) ≃ₗ[ZMod 2] ZMod 2 :=
  (NativeUnitEvaluationKernelRoute.ordinaryHomology (m + 1) (m + 1)).symm.trans (fullScalarEquiv m hm P v₀)

theorem full_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    Module.finrank (ZMod 2) (homologyZMod2 (fullPair (m + 1)).fst (m + 1)) = 1 := by
  rw [(fullScalarEquiv m hm P v₀).finrank_eq, Module.finrank_self]

theorem h1_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    Module.finrank (ZMod 2) (homologyZMod2 (Loops (m + 1)) (m + 1)) = 1 := by
  rw [(h1ScalarEquiv m hm P v₀).finrank_eq, Module.finrank_self]

theorem ordinary_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    Module.finrank (ZMod 2) (homologyZMod2 (ContinuousLoopModel.space (m + 1)) (m + 1)) = 1 := by
  rw [(ordinaryScalarEquiv m hm P v₀).finrank_eq, Module.finrank_self]

theorem full_class_eq_constant_image (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (z : homologyZMod2 (fullPair (m + 1)).fst (m + 1)) :
    z = (homologyPushZMod2 (SphereTopClass.fullSection (m + 1)) (m + 1)).hom
      ((homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom z) := by
  apply NativeConstantUnitFromPathMV.full_evaluation_injective m hm P v₀
  rw [SplitPairHomologyKernel.push_comp_apply, SphereTopClass.fullSection_eval,
    SplitPairHomologyKernel.push_id_apply]

end
end Finsler.NativeDegreeNLoopHomology
