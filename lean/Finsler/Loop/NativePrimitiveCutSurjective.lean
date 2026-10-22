module

public import Finsler.Loop.CanonicalAfterLengthProductFull
public import Finsler.Loop.NativeControlledUnitAction

/-! The ACTUAL global D_omega is onto in every output degree for
n>=3. Its preimages are full images of the SAME genuine filtered
Theta-product, with a fixed additive length cost. No abstract
surjectivity or global product is supplied as an input. -/
@[expose] public section
namespace Finsler.NativePrimitiveCutSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem cut_full_apply {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (h : a ≤ b)
    (k : ℕ) (z : homologyZMod2 (lengthSpace F a) k) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) k).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F h) k).hom z) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) k).hom z := by
  rw [push_comp_apply]
  rfl

theorem exists_positive_length_lift {n : ℕ} (F : ReversibleMetric n) (k : ℕ)
    (z : homologyZMod2 (Loops n) k) :
    ∃ b : ℝ, ∃ _hb : 0 < b, ∃ y : homologyZMod2 (lengthSpace F b) k,
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) k).hom y = z := by
  have : PreservesFilteredColimitsOfSize.{0,0} (forget (ModuleCat.{0} (ZMod 2))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨a, y, hy⟩ := Concrete.isColimit_exists_rep _
    (StrictLengthHomologyStabilization.homologyColimit F k) z
  have hy' : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) k).hom y = z := hy
  refine ⟨max a 1, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _),
    (homologyPushZMod2 (LengthFilteredLoopRotation.cut F (le_max_left a 1)) k).hom y, ?_⟩
  rw [cut_full_apply]
  exact hy'

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def raised (q : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (y : homologyZMod2 (lengthSpace F q) k) :
    homologyZMod2 (lengthSpace F (NativeThetaLengthCut.bound F P v₀ + (q + ε))) ((m + m) + k) :=
  StrictLengthLoopProduct.product F (by omega) hε ((m + m) + (m + 1)) k ((m + m) + k)
    (by omega) (NativeThetaLengthCut.input m (by omega) F P v₀) y

theorem raised_cut_full (q : ℝ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε)
    (k : ℕ) (y : homologyZMod2 (lengthSpace F q) k) :
    (CanonicalGlobalSelfCut.map m m k (MeridianLoopClass.H1TransgressionClass m)).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F
        (NativeThetaLengthCut.bound F P v₀ + (q + ε))) ((m + m) + k)).hom
          (raised m hm F P v₀ q hε k y)) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F q) k).hom y := by
  obtain ⟨B, hB, hA, hI⟩ := NativeControlledUnitAction.exists_interchange_left_inverse m hm F P v₀ hε
  let a := NativeThetaLengthCut.bound F P v₀
  let A := a + q + ε
  have hab : a + q < A := by dsimp [A]; linarith
  let T := classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)
  have hT := classRepr_isCocycle (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)
  have hs := NativeThetaLengthCut.empty_support F m T
  let v := ((CanonicalAfterLengthProduct.operation F hab hε m T hT hs).homology k).hom
    (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F q)
      ((m + m) + (m + 1)) k (((m + 1) + (m + m)) + k) (by omega)
      (NativeThetaLengthCut.input m (by omega) F P v₀) y)
  have hi := congrArg (homologyPushZMod2 (LengthFilteredLoopRotation.full F (B + q + 3 * ε)) k).hom
    (hI q hq k y)
  change (homologyPushZMod2 (LengthFilteredLoopRotation.full F (B + q + 3 * ε)) k).hom
    ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F
      (by dsimp [A, a]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε)) k).hom v) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (B + q + 3 * ε)) k).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F
        (by linarith : q ≤ B + q + 3 * ε)) k).hom y) at hi
  rw [cut_full_apply, cut_full_apply] at hi
  have hg := CanonicalAfterLengthProductFull.value (by omega) F hab hε m T hT hs
    ((m + m) + (m + 1)) k k (by omega) (NativeThetaLengthCut.input m (by omega) F P v₀) y
  have hc : cocycleClass (Loops (m + 1)) m T hT = MeridianLoopClass.H1TransgressionClass m :=
    cocycleClass_classRepr _ _ _
  rw [hc] at hg
  exact hg.symm.trans hi

include hm F P v₀ in
theorem map_surjective (k : ℕ) :
    Function.Surjective (CanonicalGlobalSelfCut.map m m k
      (MeridianLoopClass.H1TransgressionClass m)).hom := by
  intro z
  obtain ⟨q, hq, y, hy⟩ := exists_positive_length_lift F k z
  refine ⟨(homologyPushZMod2 (LengthFilteredLoopRotation.full F
    (NativeThetaLengthCut.bound F P v₀ + (q + 1))) ((m + m) + k)).hom
      (raised m hm F P v₀ q (by norm_num) k y), ?_⟩
  exact (raised_cut_full m hm F P v₀ q hq (by norm_num) k y).trans hy

end
end Finsler.NativePrimitiveCutSurjective
