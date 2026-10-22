module

public import Finsler.Loop.NativeThetaCoefficientOne
public import Finsler.Loop.SplitPairHomologyKernel
public import Finsler.Topology.AbsoluteFilteredUnits

/-! The actual original cutTheta minus the EXISTING constant-loop
unit lies in the true evaluation kernel. The real long exact sequence
reduces their equality to ZERO of this ONE original constant-relative
cut class, without requiring an entire loop-space rank calculation. -/
@[expose] public section
namespace Finsler.NativeConstantUnitDefect
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.BorelEvaluation Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def retraction (n : ℕ) : (fullPair n).fst ⟶ (fullPair n).snd := fullEval n ≫ ConstantLoopModel.fromSphere n

theorem retraction_section (n : ℕ) : (fullPair n).map ≫ retraction n = 𝟙 (fullPair n).snd := by
  have he : (fullPair n).map ≫ fullEval n = ConstantLoopModel.toSphere n := by ext z : 1; rfl
  rw [retraction, ← Category.assoc, he, ConstantLoopModel.to_from]
  rfl

theorem constant_factor (n : ℕ) : ConstantLoopModel.fromSphere n ≫ (fullPair n).map = AbsoluteFilteredUnits.constant n := by
  ext z : 1
  rfl

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

def cutFull : homologyZMod2 (fullPair (m + 1)).fst (m + 1) :=
  (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom (MeridianThetaCutCoefficient.cutTheta m hm P v₀)

def relativeCut : ((fullPair (m + 1)).singularHomology coeff (m + 1) : ModuleCat.{0} (ZMod 2)) :=
  ConstantRelativePairing.homologyToRelative (m + 1) (m + 1) (MeridianThetaCutCoefficient.cutTheta m hm P v₀)

def defect : homologyZMod2 (fullPair (m + 1)).fst (m + 1) :=
  let u : homologyZMod2 (fullPair (m + 1)).fst (m + 1) := AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega)
  cutFull m hm P v₀ - u

theorem cutFull_evaluation : (homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom (cutFull m hm P v₀) =
    SphereUnitCandidate.fundamental (m + 1) (by omega) := by
  rw [cutFull, push_comp_apply]
  exact NativeThetaCoefficientOne.cut_evaluation_fundamental m hm P v₀

theorem project_cut :
    (homologyPushZMod2 (fullPair (m + 1)).map (m + 1)).hom
      ((homologyPushZMod2 (retraction (m + 1)) (m + 1)).hom (cutFull m hm P v₀)) =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  rw [retraction, ← push_comp_apply, cutFull_evaluation, push_comp_apply, constant_factor]
  rfl

theorem defect_evaluation_zero : (homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom (defect m hm P v₀) = 0 := by
  rw [defect, map_sub, cutFull_evaluation]
  have he := AbsoluteFilteredUnits.absolute_evaluation (m + 1) (by omega)
  change (homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom
    (AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega)) = _ at he
  rw [he, sub_self]

theorem unit_iff_relative_zero : cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) ↔
    relativeCut m hm P v₀ = 0 := by
  have he := quotient_zero_iff (fullPair (m + 1)) (retraction (m + 1)) (retraction_section (m + 1)) (m + 1) (cutFull m hm P v₀)
  rw [project_cut] at he
  exact he.symm

theorem defect_zero_iff_unit : defect m hm P v₀ = 0 ↔
    cutFull m hm P v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := sub_eq_zero

theorem quotient_defect : ((fullPair (m + 1)).singularHomologyπ coeff (m + 1)).hom (defect m hm P v₀) =
    relativeCut m hm P v₀ := by
  have he := SplitPairHomologyKernel.quotient_defect (fullPair (m + 1)) (retraction (m + 1)) (m + 1) (cutFull m hm P v₀)
  unfold SplitPairHomologyKernel.defect at he
  change ((fullPair (m + 1)).singularHomologyπ coeff (m + 1)).hom
    (cutFull m hm P v₀ - (homologyPushZMod2 (fullPair (m + 1)).map (m + 1)).hom
      ((homologyPushZMod2 (retraction (m + 1)) (m + 1)).hom (cutFull m hm P v₀))) = _ at he
  rw [project_cut] at he
  exact he

end
end Finsler.NativeConstantUnitDefect
