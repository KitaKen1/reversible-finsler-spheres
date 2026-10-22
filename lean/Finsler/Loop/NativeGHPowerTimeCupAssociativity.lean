module

public import Finsler.Loop.NativeNestedTimeCupAlignment
public import Finsler.Loop.CanonicalGlobalTimeCup

/-! Restricted associativity for the SAME actual GH powers and every
positive-degree retained cohomology class. Actual normalized representatives
and the proved full source comparison discharge the geometric input.
This is the restricted comparison needed for the original high-power UNIT. -/
@[expose] public section
namespace Finsler.NativeGHPowerTimeCupAssociativity
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.NativeInnerCutPullback Finsler.NativeNestedTimeCupAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem cochain_class (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0) :
    cocycleClass _ ((m + p) + q) (GeometricTimeCupCochain.cochain m p hρ hρr hr T q B)
      (GeometricTimeCupCochain.closed m p hρ hρr hr T q B hT hB) =
      CanonicalGlobalTimeCup.product m p q (cocycleClass _ p T hT) (cocycleClass _ q B hB) :=
  (GlobalTimeCupCohomology.product_cocycle m hρ hρr hr p q T B hT hB).symm.trans
    (CanonicalGlobalTimeCup.product_compare m hm p q hρ hρr hr _ _)

theorem cast_trans (X : TopCat.{0}) {i j k : ℕ} (h : i = j) (h' : j = k)
    (a : cohomologyZMod2 X i) :
    CupUnit.absoluteCast X h' (CupUnit.absoluteCast X h a) = CupUnit.absoluteCast X (h.trans h') a := by
  subst j k
  rfl

theorem product_cast_right (m p : ℕ) {q q' : ℕ} (h : q = q')
    (A : cohomologyZMod2 (Loops (m + 1)) p) (B : cohomologyZMod2 (Loops (m + 1)) q) :
    CanonicalGlobalTimeCup.product m p q' A (CupUnit.absoluteCast (Loops (m + 1)) h B) =
      CupUnit.absoluteCast (Loops (m + 1)) (congrArg (fun n => (m + p) + n) h)
        (CanonicalGlobalTimeCup.product m p q A B) := by
  subst q'
  rfl

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem power_class (r : ℕ) : cocycleClass (Loops (m + 1)) (NativeGHPowers.degree m r)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r) =
      NativeGHPowers.power m r := NativeClosingArcPowerVanishing.powerCocycle_class m hm F r

theorem left_class (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cocycleClass _ (NativeGHProductRawAlignment.squareDegree m a b k + 1)
      (leftValue m hm F a b k E) (left_closed m hm F a b k E hE) =
      CupUnit.absoluteCast (Loops (m + 1)) (left_degree m hm a b k).symm
        (CanonicalGlobalTimeCup.product m (NativePrefixFullTimeCup.innerDegree m a b) k
          (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
            (NativeGHPowers.power m a) (NativeGHPowers.power m b)) (cocycleClass _ k E hE)) := by
  have ha := NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a
  have hb := NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b
  have hab := GeometricTimeCupCochain.closed m (NativeGHPowers.degree m a)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) _ (NativeGHPowers.degree m b) _ ha hb
  have hall := GeometricTimeCupCochain.closed m (NativePrefixFullTimeCup.innerDegree m a b)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (innerLeft m hm F a b) k E hab hE
  unfold leftValue
  rw [CochainDegreeTransport.class_cast _ _ _ hall,
    cochain_class m (by omega) _ _ _ _ _ _ _ hab hE,
    cochain_class m (by omega) _ _ _ _ _ _ _ ha hb, power_class, power_class]

theorem right_class (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cocycleClass _ (NativeGHProductRawAlignment.squareDegree m a b k + 1)
      (rightValue m hm F a b k E) (right_closed m hm F a b k E hE) =
      CupUnit.absoluteCast (Loops (m + 1)) (right_degree m hm a b k).symm
        (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m a) (NativeSuffixFullTimeCup.innerDegree m b k)
          (NativeGHPowers.power m a)
          (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m b) k (NativeGHPowers.power m b) (cocycleClass _ k E hE))) := by
  have ha := NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a
  have hb := NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b
  have hbe := GeometricTimeCupCochain.closed m (NativeGHPowers.degree m b)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) _ k E hb hE
  have hall := GeometricTimeCupCochain.closed m (NativeGHPowers.degree m a)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) _ (NativeSuffixFullTimeCup.innerDegree m b k)
    (innerRight m hm F b k E) ha hbe
  unfold rightValue
  rw [CochainDegreeTransport.class_cast _ _ _ hall,
    cochain_class m (by omega) _ _ _ _ _ _ _ ha hbe,
    cochain_class m (by omega) _ _ _ _ _ _ _ hb hE, power_class, power_class]

include F in
theorem associativity (hk : 1 ≤ k) (B : cohomologyZMod2 (Loops (m + 1)) k) :
    CupUnit.absoluteCast (Loops (m + 1)) (left_degree m hm a b k).symm
      (CanonicalGlobalTimeCup.product m (NativePrefixFullTimeCup.innerDegree m a b) k
        (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
          (NativeGHPowers.power m a) (NativeGHPowers.power m b)) B) =
    CupUnit.absoluteCast (Loops (m + 1)) (right_degree m hm a b k).symm
      (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m a) (NativeSuffixFullTimeCup.innerDegree m b k)
        (NativeGHPowers.power m a)
        (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m b) k (NativeGHPowers.power m b) B)) := by
  let E := SingularNormalization.normalize (Loops (m + 1)) k (classRepr _ k B)
  have hc : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0 :=
    SingularNormalization.normalize_closed _ _ _ (classRepr_isCocycle _ k B)
  have hn : AlgebraicTopology.DoldKan.DegeneraciesVanish
      (X := SingularNormalization.linearization (Loops (m + 1))) E := SingularNormalization.normalize_degeneracies _ _ _
  have he : cocycleClass _ k E hc = B :=
    (SingularNormalization.normalize_class_pos _ k hk _ (classRepr_isCocycle _ k B)).trans (cocycleClass_classRepr _ k B)
  have h := NativeNestedTimeCupAlignment.class_eq m hm F a b k E hc hn
  rw [left_class m hm F a b k E hc, right_class m hm F a b k E hc, he] at h
  exact h

include hm F in
theorem associativity_at_degree (hk : 1 ≤ k) (B : cohomologyZMod2 (Loops (m + 1)) k)
    (N : ℕ) (hL : leftDegree m a b k = N) (hR : rightDegree m a b k = N) :
    CupUnit.absoluteCast (Loops (m + 1)) hL
      (CanonicalGlobalTimeCup.product m (NativePrefixFullTimeCup.innerDegree m a b) k
        (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
          (NativeGHPowers.power m a) (NativeGHPowers.power m b)) B) =
    CupUnit.absoluteCast (Loops (m + 1)) hR
      (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m a) (NativeSuffixFullTimeCup.innerDegree m b k)
        (NativeGHPowers.power m a)
        (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m b) k (NativeGHPowers.power m b) B)) := by
  have h := congrArg (CupUnit.absoluteCast (Loops (m + 1)) ((left_degree m hm a b k).trans hL))
    (associativity m hm F a b k hk B)
  simpa only [cast_trans] using h

end
end Finsler.NativeGHPowerTimeCupAssociativity
