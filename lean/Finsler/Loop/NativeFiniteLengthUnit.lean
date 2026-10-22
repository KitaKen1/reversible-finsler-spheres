module

public import Finsler.Loop.StrictLengthHomologyStabilization
public import Finsler.Loop.StrictLengthFilteredUnit
public import Finsler.Loop.NativeConstantUnitFromPathMV
public import Finsler.Loop.NativeThetaLengthCut

/-! The SAME genuine filtered cut of the SAME original Theta becomes
the actual constant unit in ONE finite strict Finsler length cut.
That bound is chosen before every later degree, input class and product
length threshold. No uniform filling or high-power identity is assumed. -/
@[expose] public section
namespace Finsler.NativeFiniteLengthUnit
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem cut_full_eq_candidate {ε : ℝ} (hε : 0 < ε) (b : ℝ) (hb : 0 < b) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F
      (NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε)) (m + 1)).hom
        (NativeThetaLengthCut.cut m (by omega) F P v₀ hε) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) (m + 1)).hom
      (StrictLengthFilteredUnit.candidate F (by omega) b hb) := by
  have hi : Function.Injective (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom := by
    intro x y h
    have h' := congrArg (homologyPushZMod2 (FullLoopModel.forget (m + 1)) (m + 1)).hom h
    simpa only [push_comp_apply, FullLoopModel.include_forget, push_id_apply] using h'
  apply hi
  have hcut : (homologyPushZMod2 (LengthFilteredLoopRotation.full F
      (NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε)) (m + 1)).hom
        (NativeThetaLengthCut.cut m (by omega) F P v₀ hε) =
      MeridianThetaCutCoefficient.cutTheta m (by omega) P v₀ :=
    NativeThetaLengthCut.cut_full m (by omega) F P v₀ hε
  have hunit : (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
      (MeridianThetaCutCoefficient.cutTheta m (by omega) P v₀) =
        AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
    NativeConstantUnitFromPathMV.original_UNIT m hm P v₀
  exact (congrArg (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom hcut).trans
    (hunit.trans (StrictLengthFilteredUnit.candidate_full F (by omega) b hb).symm)

theorem exists_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∃ hB : 0 < B,
      ∃ hA : NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε ≤ B,
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hA) (m + 1)).hom
          (NativeThetaLengthCut.cut m (by omega) F P v₀ hε) =
            StrictLengthFilteredUnit.candidate F (by omega) B hB := by
  obtain ⟨B, hA, h1, he⟩ := StrictLengthHomologyStabilization.exists_equal F (m + 1)
    (NativeThetaLengthCut.cut m (by omega) F P v₀ hε)
    (StrictLengthFilteredUnit.candidate F (by omega) 1 (by norm_num))
    (cut_full_eq_candidate m hm F P v₀ hε 1 (by norm_num))
  have hB : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h1
  exact ⟨B, hB, hA, he.trans
    (StrictLengthFilteredUnit.candidate_cut F (by omega) (by norm_num) hB h1)⟩

theorem exists_all_degree_left_unit {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∃ hB : 0 < B,
      ∃ hA : NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε ≤ B,
        ∀ (q δ : ℝ) (_hq : 0 < q) (hδ : 0 < δ) (k : ℕ)
          (y : homologyZMod2 (lengthSpace F q) k),
          StrictLengthLoopProduct.product F (by omega) hδ (m + 1) k k rfl
            ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F hA) (m + 1)).hom
              (NativeThetaLengthCut.cut m (by omega) F P v₀ hε)) y =
            (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
              (by linarith : q ≤ B + (q + δ))) k).hom y := by
  obtain ⟨B, hB, hA, he⟩ := exists_bound m hm F P v₀ hε
  refine ⟨B, hB, hA, ?_⟩
  intro q δ hq hδ k y
  exact (congrArg (fun z : homologyZMod2 (lengthSpace F B) (m + 1) =>
    StrictLengthLoopProduct.product F (by omega) hδ (m + 1) k k rfl z y) he).trans
      (StrictLengthFilteredUnit.left_unit F (by omega) hB hq hδ k y)

end
end Finsler.NativeFiniteLengthUnit
