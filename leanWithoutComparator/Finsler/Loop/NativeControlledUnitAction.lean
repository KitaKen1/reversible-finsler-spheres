module

public import Finsler.Loop.NativeFiniteLengthUnit
public import Finsler.Loop.StrictLengthProductFirstNaturality
public import Finsler.Loop.FilteredCanonicalInterchange

/-! The original filtered cutTheta acts on EVERY degree after ONE
bounded enlargement, even when the product is formed BEFORE that
enlargement. Apply the existing genuine filtered interchange to the
same original Theta, not to an abstract product or chosen new cut. -/
@[expose] public section
namespace Finsler.NativeControlledUnitAction
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem exists_stabilized_left_unit {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∃ hB : 0 < B,
      ∃ hA : NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε ≤ B,
        ∀ (q δ : ℝ) (_hq : 0 < q) (hδ : 0 < δ) (k : ℕ)
          (y : homologyZMod2 (lengthSpace F q) k),
          (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
            (by linarith : (NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε) + (q + δ) ≤
              B + (q + δ))) k).hom
            (StrictLengthLoopProduct.product F (by omega) hδ (m + 1) k k rfl
              (NativeThetaLengthCut.cut m (by omega) F P v₀ hε) y) =
          (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
            (by linarith : q ≤ B + (q + δ))) k).hom y := by
  obtain ⟨B, hB, hA, he⟩ := NativeFiniteLengthUnit.exists_bound m hm F P v₀ hε
  refine ⟨B, hB, hA, ?_⟩
  intro q δ hq hδ k y
  have hC : 0 < NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε := by
    linarith [NativeThetaLengthCut.bound_positive F P v₀]
  have hN := StrictLengthProductFirstNaturality.product_naturality F hC hB hq hδ hA
    (by omega) (m + 1) k k rfl (NativeThetaLengthCut.cut m (by omega) F P v₀ hε) y
  exact hN.symm.trans
    ((congrArg (fun z : homologyZMod2 (lengthSpace F B) (m + 1) =>
      StrictLengthLoopProduct.product F (by omega) hδ (m + 1) k k rfl z y) he).trans
        (StrictLengthFilteredUnit.left_unit F (by omega) hB hq hδ k y))

theorem exists_interchange_left_inverse {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∃ hB : 0 < B,
      ∃ hA : NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε ≤ B,
        ∀ (q : ℝ) (_hq : 0 < q) (k : ℕ) (y : homologyZMod2 (lengthSpace F q) k),
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
          (by linarith : (NativeThetaLengthCut.bound F P v₀ + q + ε) - 0 + 5 * ε ≤
            B + q + 3 * ε)) k).hom
          (((CanonicalAfterLengthProduct.operation F
            (by linarith : NativeThetaLengthCut.bound F P v₀ + q <
              NativeThetaLengthCut.bound F P v₀ + q + ε) hε m
            (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))
            (classRepr_isCocycle _ m _) (NativeThetaLengthCut.empty_support F m _)).homology k).hom
            (FilteredBilinearLoopProduct.cross
              (lengthSpace F (NativeThetaLengthCut.bound F P v₀)) (lengthSpace F q)
              ((m + m) + (m + 1)) k (((m + 1) + (m + m)) + k) (by omega)
              (NativeThetaLengthCut.input m (by omega) F P v₀) y)) =
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
          (by linarith : q ≤ B + q + 3 * ε)) k).hom y := by
  obtain ⟨B, hB, hA, hunit⟩ := exists_stabilized_left_unit m hm F P v₀ hε
  refine ⟨B, hB, hA, ?_⟩
  intro q hq k y
  let a := NativeThetaLengthCut.bound F P v₀
  let A := a + q + ε
  have hab : a + q < A := by dsimp [A]; linarith
  let T := classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)
  have hT := classRepr_isCocycle (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)
  have hs := NativeThetaLengthCut.empty_support F m T
  have hI := FilteredCanonicalInterchange.value F hε (by omega) m 0 a q A T hT hs hab
    (m + 1) k k rfl (by omega) (NativeThetaLengthCut.input m (by omega) F P v₀) y
  refine (congrArg (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
    (by dsimp [A, a]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε)) k).hom hI).trans ?_
  change (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
    (by dsimp [A, a]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε)) k).hom
    ((homologyPushZMod2 (StrictLengthProductBudget.outputInclusion F (L := 0) hab hε) k).hom
      (StrictLengthLoopProduct.product F (by omega) hε (m + 1) k k rfl
        (NativeThetaLengthCut.cut m (by omega) F P v₀ hε) y)) = _
  rw [push_comp_apply]
  have hmaps : StrictLengthProductBudget.outputInclusion F (L := 0) hab hε ≫
      LengthFilteredLoopRotation.cut F
        (by dsimp [A, a]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε) =
    LengthFilteredLoopRotation.cut F
      (by dsimp [a]; linarith : (a - 0 + 3 * ε) + (q + ε) ≤ B + (q + ε)) ≫
      LengthFilteredLoopRotation.cut F
        (by linarith : B + (q + ε) ≤ B + q + 3 * ε) := by
    ext z : 1
    rfl
  rw [hmaps, ← push_comp_apply, hunit q ε hq hε k y, push_comp_apply]
  rfl

end
end Finsler.NativeControlledUnitAction
