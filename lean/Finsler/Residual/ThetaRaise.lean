module

public import Finsler.Loop.NativeHighPowerUnit
public import Finsler.Loop.NativePrimitiveCutSurjective
public import Finsler.Loop.NativeThetaSpectralLength

/-! Raising by an arbitrary lift of the r-th Theta power (Claude, full-HR prototype).

`NativePrimitiveCutSurjective.raised_cut_full` shows that the global cut by the primitive GH class
ω inverts the filtered loop product with the primitive Theta input. The same argument works for a
cutting cocycle T of any degree p whose global cut sends the global image of a filtered class z to
the constant unit: the filtered cut of z becomes the filtered unit at one finite length
(`exists_bound`), the filtered interchange turns the cut of z • y into (cut z) • y, and the left
unit gives D_T(z • y) = y (`raise_cut_full`). For T the r-th GH power and z ANY filtered lift of
the r-th Theta power the unit equation is the high-power UNIT (`NativeHighPowerUnit.single_UNIT`),
so the loop product with a near-optimal lift of the r-th Theta power is injective on homology and
costs only the Theta level (`theta_raise_ne_zero`). -/

@[expose] public section

namespace Finsler.ThetaRaise

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
  (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
  {a : ℝ} (z : homologyZMod2 (lengthSpace F a) ((m + p) + (m + 1)))

/-- The filtered cut of z by T (empty short support). -/
def cutZ {ε : ℝ} (hε : 0 < ε) : homologyZMod2 (lengthSpace F (a - 0 + 3 * ε)) (m + 1) :=
  ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT
    (NativeThetaLengthCut.empty_support F p T) (a := a)).homology (m + 1)).hom z

/-- The global unit equation for the cut of z. -/
def UnitEq : Prop :=
  (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
    ((CanonicalGlobalSelfCut.map m p (m + 1) (cocycleClass _ p T hT)).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F a) ((m + p) + (m + 1))).hom z)) =
    AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega)

variable {m F p T hT z}

include hm in
theorem cut_full_eq_candidate (hunit : UnitEq m hm F p T hT z) {ε : ℝ} (hε : 0 < ε) (b : ℝ)
    (hb : 0 < b) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a - 0 + 3 * ε)) (m + 1)).hom
        (cutZ m F p T hT z hε) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) (m + 1)).hom
      (StrictLengthFilteredUnit.candidate F (by omega) b hb) := by
  have hi : Function.Injective (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom := by
    intro x y h
    have h' := congrArg (homologyPushZMod2 (FullLoopModel.forget (m + 1)) (m + 1)).hom h
    simpa only [push_comp_apply, FullLoopModel.include_forget, push_id_apply] using h'
  apply hi
  have hcut : (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a - 0 + 3 * ε)) (m + 1)).hom
      (cutZ m F p T hT z hε) =
      (CanonicalGlobalSelfCut.map m p (m + 1) (cocycleClass _ p T hT)).hom
        ((homologyPushZMod2 (LengthFilteredLoopRotation.full F a) ((m + p) + (m + 1))).hom z) :=
    CanonicalGlobalSelfCutFiltered.original_filtered m (by omega) p F hε T hT
      (NativeThetaLengthCut.empty_support F p T) (m + 1) z
  rw [hcut]
  exact hunit.trans (StrictLengthFilteredUnit.candidate_full F (by omega) b hb).symm

include hm in
/-- The filtered cut of z is the filtered unit at one finite length. -/
theorem exists_bound (hunit : UnitEq m hm F p T hT z) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∃ hB : 0 < B, ∃ hA : a - 0 + 3 * ε ≤ B,
      (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hA) (m + 1)).hom
          (cutZ m F p T hT z hε) =
        StrictLengthFilteredUnit.candidate F (by omega) B hB := by
  obtain ⟨B, hA, h1, he⟩ := StrictLengthHomologyStabilization.exists_equal F (m + 1)
    (cutZ m F p T hT z hε)
    (StrictLengthFilteredUnit.candidate F (by omega) 1 (by norm_num))
    (cut_full_eq_candidate hm hunit hε 1 (by norm_num))
  have hB : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h1
  exact ⟨B, hB, hA, he.trans
    (StrictLengthFilteredUnit.candidate_cut F (by omega) (by norm_num) hB h1)⟩

include hm in
theorem exists_stabilized_left_unit (hunit : UnitEq m hm F p T hT z) (ha : 0 < a) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ B : ℝ, ∃ hB : 0 < B, ∃ hA : a - 0 + 3 * ε ≤ B,
      ∀ (q δ : ℝ) (_hq : 0 < q) (hδ : 0 < δ) (k : ℕ)
        (y : homologyZMod2 (lengthSpace F q) k),
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
          (by linarith : (a - 0 + 3 * ε) + (q + δ) ≤ B + (q + δ))) k).hom
          (StrictLengthLoopProduct.product F (by omega) hδ (m + 1) k k rfl
            (cutZ m F p T hT z hε) y) =
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
          (by linarith : q ≤ B + (q + δ))) k).hom y := by
  obtain ⟨B, hB, hA, he⟩ := exists_bound hm hunit hε
  refine ⟨B, hB, hA, ?_⟩
  intro q δ hq hδ k y
  have hC : 0 < a - 0 + 3 * ε := by linarith
  have hN := StrictLengthProductFirstNaturality.product_naturality F hC hB hq hδ hA
    (by omega) (m + 1) k k rfl (cutZ m F p T hT z hε) y
  exact hN.symm.trans
    ((congrArg (fun w : homologyZMod2 (lengthSpace F B) (m + 1) =>
      StrictLengthLoopProduct.product F (by omega) hδ (m + 1) k k rfl w y) he).trans
        (StrictLengthFilteredUnit.left_unit F (by omega) hB hq hδ k y))

include hm in
theorem exists_interchange_left_inverse (hunit : UnitEq m hm F p T hT z) (ha : 0 < a) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ B : ℝ, ∃ hB : 0 < B, ∃ hA : a - 0 + 3 * ε ≤ B,
      ∀ (q : ℝ) (_hq : 0 < q) (k : ℕ) (y : homologyZMod2 (lengthSpace F q) k),
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
          (by linarith : (a + q + ε) - 0 + 5 * ε ≤ B + q + 3 * ε)) k).hom
          (((CanonicalAfterLengthProduct.operation F
            (by linarith : a + q < a + q + ε) hε p T hT
            (NativeThetaLengthCut.empty_support F p T)).homology k).hom
            (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F q)
              ((m + p) + (m + 1)) k (((m + 1) + (m + p)) + k) (by omega) z y)) =
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
          (by linarith : q ≤ B + q + 3 * ε)) k).hom y := by
  obtain ⟨B, hB, hA, hunit'⟩ := exists_stabilized_left_unit hm hunit ha hε
  refine ⟨B, hB, hA, ?_⟩
  intro q hq k y
  let A := a + q + ε
  have hab : a + q < A := by dsimp [A]; linarith
  have hI := FilteredCanonicalInterchange.value F hε (by omega) p 0 a q A T hT
    (NativeThetaLengthCut.empty_support F p T) hab (m + 1) k k rfl (by omega) z y
  refine (congrArg (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
    (by dsimp [A]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε)) k).hom hI).trans ?_
  change (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
    (by dsimp [A]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε)) k).hom
    ((homologyPushZMod2 (StrictLengthProductBudget.outputInclusion F (L := 0) hab hε) k).hom
      (StrictLengthLoopProduct.product F (by omega) hε (m + 1) k k rfl
        (cutZ m F p T hT z hε) y)) = _
  rw [push_comp_apply]
  have hmaps : StrictLengthProductBudget.outputInclusion F (L := 0) hab hε ≫
      LengthFilteredLoopRotation.cut F
        (by dsimp [A]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε) =
    LengthFilteredLoopRotation.cut F
      (by linarith : (a - 0 + 3 * ε) + (q + ε) ≤ B + (q + ε)) ≫
      LengthFilteredLoopRotation.cut F
        (by linarith : B + (q + ε) ≤ B + q + 3 * ε) := by
    ext w : 1
    rfl
  rw [hmaps, ← push_comp_apply, hunit' q ε hq hε k y, push_comp_apply]
  rfl

include hm in
/-- **The global cut by T inverts the filtered loop product with z.** -/
theorem raise_cut_full (hunit : UnitEq m hm F p T hT z) (ha : 0 < a) (q : ℝ) (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (y : homologyZMod2 (lengthSpace F q) k) :
    (CanonicalGlobalSelfCut.map m p k (cocycleClass _ p T hT)).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (a + (q + ε))) ((m + p) + k)).hom
        (StrictLengthLoopProduct.product F (by omega) hε ((m + p) + (m + 1)) k ((m + p) + k)
          (by omega) z y)) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F q) k).hom y := by
  obtain ⟨B, hB, hA, hI⟩ := exists_interchange_left_inverse hm hunit ha hε
  let A := a + q + ε
  have hab : a + q < A := by dsimp [A]; linarith
  have hs := NativeThetaLengthCut.empty_support F p T
  let v := ((CanonicalAfterLengthProduct.operation F hab hε p T hT hs).homology k).hom
    (FilteredBilinearLoopProduct.cross (lengthSpace F a) (lengthSpace F q)
      ((m + p) + (m + 1)) k (((m + 1) + (m + p)) + k) (by omega) z y)
  have hi := congrArg (homologyPushZMod2 (LengthFilteredLoopRotation.full F (B + q + 3 * ε)) k).hom
    (hI q hq k y)
  change (homologyPushZMod2 (LengthFilteredLoopRotation.full F (B + q + 3 * ε)) k).hom
    ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F
      (by dsimp [A]; linarith : A - 0 + 5 * ε ≤ B + q + 3 * ε)) k).hom v) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (B + q + 3 * ε)) k).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F
        (by linarith : q ≤ B + q + 3 * ε)) k).hom y) at hi
  rw [NativePrimitiveCutSurjective.cut_full_apply, NativePrimitiveCutSurjective.cut_full_apply] at hi
  have hg := CanonicalAfterLengthProductFull.value (by omega) F hab hε p T hT hs
    ((m + p) + (m + 1)) k k (by omega) z y
  exact hg.symm.trans hi

theorem push_eqToHom {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (x : homologyZMod2 X i) :
    (homologyPushZMod2 f j).hom ((eqToHom (congrArg (homologyZMod2 X) h)).hom x) =
      (eqToHom (congrArg (homologyZMod2 Y) h)).hom ((homologyPushZMod2 f i).hom x) := by
  subst h
  rfl

variable (m) (F) (P : Sphere (m + 1)) (v₀ : equator P)

/-- A filtered class of the Theta degree, cast to the aligned degree of the cut. -/
def aligned (r : ℕ) {a : ℝ} (z₀ : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r)) :
    homologyZMod2 (lengthSpace F a) ((m + NativeGHPowers.degree m r) + (m + 1)) :=
  (eqToHom (congrArg (homologyZMod2 (lengthSpace F a))
    (NativeHighPowerUnitComparison.degree_match m r))).hom z₀

/-- The high-power UNIT for every filtered lift of the r-th Theta power. -/
theorem unitEq_of_lift (r : ℕ) {a : ℝ}
    (z₀ : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) _).hom z₀ =
      NativeThetaPowers.fullPower m hm F P v₀ r) :
    UnitEq m hm F (NativeGHPowers.degree m r)
      (classRepr _ _ (NativeGHPowers.power m r)) (classRepr_isCocycle _ _ _) (aligned m F r z₀) := by
  unfold UnitEq
  rw [cocycleClass_classRepr, aligned, push_eqToHom _ (NativeHighPowerUnitComparison.degree_match m r), hz]
  exact NativeHighPowerUnit.single_UNIT m hm F P v₀ r

/-- **The r-th GH power cut inverts the loop product with any lift of the r-th Theta power.** -/
theorem theta_raise_cut (r : ℕ) {a : ℝ} (ha : 0 < a)
    (z₀ : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) _).hom z₀ =
      NativeThetaPowers.fullPower m hm F P v₀ r)
    (q : ℝ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (y : homologyZMod2 (lengthSpace F q) k) :
    (CanonicalGlobalSelfCut.map m (NativeGHPowers.degree m r) k (NativeGHPowers.power m r)).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (a + (q + ε)))
        ((m + NativeGHPowers.degree m r) + k)).hom
        (StrictLengthLoopProduct.product F (by omega) hε ((m + NativeGHPowers.degree m r) + (m + 1)) k
          ((m + NativeGHPowers.degree m r) + k) (by omega) (aligned m F r z₀) y)) =
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F q) k).hom y := by
  have h := raise_cut_full hm (unitEq_of_lift m hm F P v₀ r z₀ hz) ha q hq hε k y
  rwa [cocycleClass_classRepr] at h

/-- **Raising by a near-optimal Theta lift.** For every length a above the Theta level and every
filtered class y with nonzero global image, the loop product with a lift at length a has nonzero
global image, carried at length a + (q + ε). -/
theorem theta_raise_ne_zero (r : ℕ) {a : ℝ} (ha : NativeThetaSpectralLength.level m hm F P v₀ r < a)
    (q : ℝ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (y : homologyZMod2 (lengthSpace F q) k)
    (hy : (homologyPushZMod2 (LengthFilteredLoopRotation.full F q) k).hom y ≠ 0) :
    ∃ Z : homologyZMod2 (lengthSpace F (a + (q + ε))) ((m + NativeGHPowers.degree m r) + k),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a + (q + ε)))
        ((m + NativeGHPowers.degree m r) + k)).hom Z ≠ 0 ∧
      (CanonicalGlobalSelfCut.map m (NativeGHPowers.degree m r) k (NativeGHPowers.power m r)).hom
        ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (a + (q + ε)))
          ((m + NativeGHPowers.degree m r) + k)).hom Z) =
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F q) k).hom y := by
  obtain ⟨z₀, hz⟩ := NativeThetaSpectralLength.lift_above m hm F P v₀ r ha
  have ha0 : 0 < a := (NativeThetaSpectralLength.level_positive m hm F P v₀ r).trans ha
  have h := theta_raise_cut m hm F P v₀ r ha0 z₀ hz q hq hε k y
  refine ⟨_, fun h0 => hy ?_, h⟩
  rw [← h, h0, map_zero]

end

end Finsler.ThetaRaise
