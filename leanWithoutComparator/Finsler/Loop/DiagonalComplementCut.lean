module

public import Finsler.Loop.DiagonalSelfCutRepresentatives
public import Finsler.Loop.NativeTripleSelfEvaluation
public import Finsler.Loop.LoopSweepTwoPiece

/-! The ACTUAL complementary self-cut (t,u)->(1-t,shift_t u) is a
continuous involution on the original coincidence locus. Its prefix
is the original suffix, and its suffix is the original prefix, at
every interval/circle point. ORIGINAL tested/retained maps are
therefore interchanged by genuine ordinary homotopies. This covers
the wrapped cut direction without assigning a Thom multiplicity. -/
@[expose] public section
namespace Finsler.DiagonalComplementCut
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.DiagonalSelfCutRepresentatives Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase
open Finsler.SobolevCircleRepresentative Finsler.SobolevShift Finsler.SobolevAffine
open Finsler.SobolevCircleAction
open Finsler.ClosedLoopReparametrization Finsler.NativeTripleSelfEvaluation
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def complement (n : ℕ) : domain n ⟶ domain n :=
  TopCat.ofHom ⟨fun z => ⟨(unitInterval.symm z.val.1, shiftSphere z.val.2 (z.val.1 : ℝ)), by
    change sphereRepresentative (shiftSphere z.val.2 (z.val.1 : ℝ)) (unitInterval.symm z.val.1) =
      point (shiftSphere z.val.2 (z.val.1 : ℝ))
    rw [endpoint_shift, point_shift]
    have ha : ((z.val.1 : ℝ) : SobolevCircleRepresentative.Circle) +
        (((unitInterval.symm z.val.1 : ℝ)) : SobolevCircleRepresentative.Circle) = 0 := by
      rw [← AddCircle.coe_add]
      change (((z.val.1 : ℝ) + (1 - (z.val.1 : ℝ)) : ℝ) : SobolevCircleRepresentative.Circle) = 0
      rw [show (z.val.1 : ℝ) + (1 - (z.val.1 : ℝ)) = 1 by ring, AddCircle.coe_period]
    rw [ha]
    have h0 := sphereCircleMap_coe z.val.2 0
    change sphereCircleMap z.val.2 0 = point z.val.2 at h0
    have ht := sphereCircleMap_coe z.val.2 z.val.1
    exact h0.trans (z.property.symm.trans ht.symm)⟩, by
    have hp : Continuous (fun z : domain n => (z.val.1, z.val.2)) := continuous_subtype_val
    have hs := (H1LoopRotation.homotopy n).continuous.comp hp
    have ht : Continuous (fun z : domain n => unitInterval.symm z.val.1) := by fun_prop
    exact (ht.prodMk (hs.congr (fun _ => rfl))).subtype_mk _⟩

theorem involution (n : ℕ) : complement n ≫ complement n = 𝟙 (domain n) := by
  ext z : 1
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change 1 - (1 - (z.val.1 : ℝ)) = (z.val.1 : ℝ)
    ring
  · change shiftSphere (shiftSphere z.val.2 (z.val.1 : ℝ)) (1 - (z.val.1 : ℝ)) = z.val.2
    rw [shiftSphere_add, show (1 - (z.val.1 : ℝ)) + (z.val.1 : ℝ) = 1 by ring]
    have hp := shiftSphere_periodic z.val.2 0
    simpa only [zero_add, shiftSphere_zero] using hp

theorem prefix_complement {n : ℕ} (z : domain n) : prefixClosed (complement n z) = suffixClosed z := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change sphereRepresentative (shiftSphere z.val.2 (z.val.1 : ℝ))
    (prefixTime (unitInterval.symm z.val.1) s) = sphereRepresentative z.val.2 (suffixTime z.val.1 s)
  rw [endpoint_shift]
  have ha : ((z.val.1 : ℝ) : SobolevCircleRepresentative.Circle) +
      ((prefixTime (unitInterval.symm z.val.1) s : ℝ) : SobolevCircleRepresentative.Circle) =
      ((suffixTime z.val.1 s : ℝ) : SobolevCircleRepresentative.Circle) := by
    rw [← AddCircle.coe_add]
    congr 1
  rw [ha, sphereCircleMap_coe]

theorem suffix_complement {n : ℕ} (z : domain n) : suffixClosed (complement n z) = prefixClosed z := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change sphereRepresentative (shiftSphere z.val.2 (z.val.1 : ℝ))
    (suffixTime (unitInterval.symm z.val.1) s) = sphereRepresentative z.val.2 (prefixTime z.val.1 s)
  rw [endpoint_shift]
  have ha : ((z.val.1 : ℝ) : SobolevCircleRepresentative.Circle) +
      ((suffixTime (unitInterval.symm z.val.1) s : ℝ) : SobolevCircleRepresentative.Circle) =
      ((prefixTime z.val.1 s : ℝ) : SobolevCircleRepresentative.Circle) := by
    rw [← AddCircle.coe_add]
    have he : (z.val.1 : ℝ) + (suffixTime (unitInterval.symm z.val.1) s : ℝ) =
        (prefixTime z.val.1 s : ℝ) + 1 := by
      change (z.val.1 : ℝ) + ((1 - (z.val.1 : ℝ)) + (1 - (1 - (z.val.1 : ℝ))) * s) = (z.val.1 : ℝ) * s + 1
      ring
    rw [he, AddCircle.coe_add_period]
  rw [ha, sphereCircleMap_coe]

theorem prefix_family_complement (n : ℕ) : complement n ≫ prefixFamily n = suffixFamily n := by
  ext z : 1
  exact prefix_complement z

theorem suffix_family_complement (n : ℕ) : complement n ≫ suffixFamily n = prefixFamily n := by
  ext z : 1
  exact suffix_complement z

def testedRetainedHomotopy (n : ℕ) : TopCat.Homotopy (complement n ≫ tested n) (retained n) := by
  rw [tested_factor, ← Category.assoc, prefix_family_complement, retained_factor]
  exact (homotopy n early late).comp (TopCat.Homotopy.refl (suffixFamily n))

def retainedTestedHomotopy (n : ℕ) : TopCat.Homotopy (complement n ≫ retained n) (tested n) := by
  rw [retained_factor, ← Category.assoc, suffix_family_complement, tested_factor]
  exact (homotopy n late early).comp (TopCat.Homotopy.refl (prefixFamily n))

theorem tested_cohomology_swap (n q : ℕ) (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (complement n ≫ tested n) q).hom a = (cohPullback (retained n) q).hom a :=
  LoopSweepTwoPiece.cohomology_homotopy (testedRetainedHomotopy n) q a

theorem retained_cohomology_swap (n q : ℕ) (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (complement n ≫ retained n) q).hom a = (cohPullback (tested n) q).hom a :=
  LoopSweepTwoPiece.cohomology_homotopy (retainedTestedHomotopy n) q a

end
end Finsler.DiagonalComplementCut
