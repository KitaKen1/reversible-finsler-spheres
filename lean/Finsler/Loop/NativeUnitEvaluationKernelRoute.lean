module

public import Finsler.Loop.NativeConstantUnitDefect
public import Finsler.Loop.ContinuousLoopHomologyEquivalence

/-! The exact native bridge for the low-degree evaluation route.
Only injectivity of the ACTUAL ordinary evaluation in degree n is
needed. All full/H1/ordinary maps and the EXISTING UNIT are retained.
That injectivity is an explicit pending input here, not an axiom or
a claimed theorem about the homology of free sphere loops. -/
@[expose] public section
namespace Finsler.NativeUnitEvaluationKernelRoute
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def fullOrdinary (n : ℕ) : (fullPair n).fst ⟶ ContinuousLoopModel.space n :=
  FullLoopModel.forget n ≫ ContinuousLoopModel.inclusion n

theorem evaluation_square (n : ℕ) :
    fullOrdinary n ≫ ContinuousLoopModel.evaluation n = BorelEvaluation.fullEval n := by
  rw [fullOrdinary, Category.assoc, ContinuousLoopModel.evaluation_square,
    ← Category.assoc, FullLoopModel.forget_include, Category.id_comp]

def fullHomology (n k : ℕ) : homologyZMod2 (fullPair n).fst k ≃ₗ[ZMod 2] homologyZMod2 (Loops n) k :=
  (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso (FullLoopModel.iso n)).toLinearEquiv

def ordinaryHomology (n k : ℕ) : homologyZMod2 (fullPair n).fst k ≃ₗ[ZMod 2]
    homologyZMod2 (ContinuousLoopModel.space n) k :=
  (fullHomology n k).trans (ContinuousLoopHomologyEquivalence.homology n k)

theorem ordinaryHomology_apply (n k : ℕ) (z : homologyZMod2 (fullPair n).fst k) :
    ordinaryHomology n k z = (homologyPushZMod2 (fullOrdinary n) k).hom z :=
  SplitPairHomologyKernel.push_comp_apply (FullLoopModel.forget n) (ContinuousLoopModel.inclusion n) k z

theorem evaluation_push_square (n k : ℕ) (z : homologyZMod2 (fullPair n).fst k) :
    (homologyPushZMod2 (ContinuousLoopModel.evaluation n) k).hom (ordinaryHomology n k z) =
      (homologyPushZMod2 (BorelEvaluation.fullEval n) k).hom z := by
  rw [ordinaryHomology_apply, SplitPairHomologyKernel.push_comp_apply, evaluation_square]

theorem full_evaluation_injective_iff (n k : ℕ) :
    Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval n) k).hom ↔
      Function.Injective (homologyPushZMod2 (ContinuousLoopModel.evaluation n) k).hom := by
  constructor
  · intro hi x y he
    obtain ⟨a, rfl⟩ := (ordinaryHomology n k).surjective x
    obtain ⟨b, rfl⟩ := (ordinaryHomology n k).surjective y
    exact congrArg (ordinaryHomology n k) (hi (by simpa only [evaluation_push_square] using he))
  · intro hi x y he
    apply (ordinaryHomology n k).injective
    exact hi (by simpa only [evaluation_push_square] using he)

theorem ordinary_retraction (n k : ℕ) (z : homologyZMod2 (BorelEvaluation.sphere n) k) :
    (homologyPushZMod2 (ContinuousLoopModel.evaluation n) k).hom
      ((homologyPushZMod2 (ContinuousLoopModel.constantMap n) k).hom z) = z := by
  rw [SplitPairHomologyKernel.push_comp_apply, ContinuousLoopModel.constant_evaluation,
    SplitPairHomologyKernel.push_id_apply]

theorem ordinary_evaluation_injective_iff_constants_surjective (n k : ℕ) :
    Function.Injective (homologyPushZMod2 (ContinuousLoopModel.evaluation n) k).hom ↔
      Function.Surjective (homologyPushZMod2 (ContinuousLoopModel.constantMap n) k).hom := by
  constructor
  · intro hi z
    refine ⟨(homologyPushZMod2 (ContinuousLoopModel.evaluation n) k).hom z, ?_⟩
    apply hi
    exact ordinary_retraction n k _
  · intro hs x y he
    obtain ⟨a, rfl⟩ := hs x
    obtain ⟨b, rfl⟩ := hs y
    rw [ordinary_retraction, ordinary_retraction] at he
    exact congrArg (homologyPushZMod2 (ContinuousLoopModel.constantMap n) k).hom he

theorem unit_of_full_evaluation_injective (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1))
    (v₀ : equator P)
    (hi : Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval (m + 1)) (m + 1)).hom) :
    NativeConstantUnitDefect.cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  apply hi
  exact (NativeConstantUnitDefect.cutFull_evaluation m hm P v₀).trans
    (AbsoluteFilteredUnits.absolute_evaluation (m + 1) (by omega)).symm

theorem unit_of_ordinary_evaluation_injective (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1))
    (v₀ : equator P)
    (hi : Function.Injective (homologyPushZMod2 (ContinuousLoopModel.evaluation (m + 1)) (m + 1)).hom) :
    NativeConstantUnitDefect.cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  unit_of_full_evaluation_injective m hm P v₀ ((full_evaluation_injective_iff (m + 1) (m + 1)).mpr hi)

theorem relativeCut_zero_of_ordinary_evaluation_injective (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1))
    (v₀ : equator P)
    (hi : Function.Injective (homologyPushZMod2 (ContinuousLoopModel.evaluation (m + 1)) (m + 1)).hom) :
    NativeConstantUnitDefect.relativeCut m hm P v₀ = 0 :=
  (NativeConstantUnitDefect.unit_iff_relative_zero m hm P v₀).mp
    (unit_of_ordinary_evaluation_injective m hm P v₀ hi)

theorem unit_of_ordinary_constants_surjective (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1))
    (v₀ : equator P)
    (hs : Function.Surjective (homologyPushZMod2 (ContinuousLoopModel.constantMap (m + 1)) (m + 1)).hom) :
    NativeConstantUnitDefect.cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  unit_of_ordinary_evaluation_injective m hm P v₀
    ((ordinary_evaluation_injective_iff_constants_surjective (m + 1) (m + 1)).mpr hs)

end
end Finsler.NativeUnitEvaluationKernelRoute
