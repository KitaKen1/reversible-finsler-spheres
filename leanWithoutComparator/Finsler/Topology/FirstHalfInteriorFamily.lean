module

public import Finsler.Topology.FirstHalfFixedOutput
public import Finsler.Topology.JoinedHalfTrim

/-! The actual trimmed first-half cylinder lifts to the existing
fixed-tested-output homotopy on its genuine cut neighborhood. The
retained length is exactly constant throughout this actual family. -/

@[expose] public section
namespace Finsler.FirstHalfInteriorFamily

open CategoryTheory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SelfCutThomCocycle
open Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {X : Type} [TopologicalSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

def firstParameters : C(ClosedInterval × X, parameters n) :=
  ⟨fun z => (InteriorTimeSlide.trimTime a ha.le ha1.le z.1, (u z.2).val.1),
    ((InteriorTimeSlide.trimTime a ha.le ha1.le).continuous.comp continuous_fst).prodMk
      ((continuous_fst.comp (continuous_subtype_val.comp u.continuous)).comp continuous_snd)⟩

def domain (r : ℝ) : Set (ClosedInterval × X) :=
  firstParameters u a ha ha1 ⁻¹' neighborhood n r

theorem domain_open (r : ℝ) : IsOpen (domain u a ha ha1 r) :=
  (neighborhood_open n r).preimage (firstParameters u a ha ha1).continuous

def input {r : ℝ} (hr : r ≤ 1) : C(domain u a ha ha1 r, FirstHalfRetainedHomotopy.inputs n) := by
  let ztube : C(domain u a ha ha1 r, tube n) :=
    ⟨fun z => ⟨firstParameters u a ha ha1 z.val, (show distance n (firstParameters u a ha ha1 z.val) < r from z.property).trans_le hr⟩,
      ((firstParameters u a ha ha1).continuous.comp continuous_subtype_val).subtype_mk _⟩
  refine ⟨fun z => ⟨(ztube z, (u z.val.2).val.2), ?_, (u z.val.2).property⟩, ?_⟩
  · change (InteriorTimeSlide.trimTime a ha.le ha1.le z.val.1 : ℝ) < 1
    exact (InteriorTimeSlide.trimTime_range a ha.le ha1.le z.val.1).2.trans_lt (by linarith)
  · exact (ztube.continuous.prodMk
      (continuous_snd.comp (continuous_subtype_val.comp
        (u.continuous.comp (continuous_snd.comp continuous_subtype_val))))).subtype_mk _

theorem joinedTube_parameters {r : ℝ} (hr : r ≤ 1) (z : domain u a ha ha1 r) :
    (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z)).val =
      CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le z.val := rfl

def family {r : ℝ} (hr : r ≤ 1) :
    C(_root_.unitInterval × domain u a ha ha1 r, SphereLoop n × SphereLoop n) :=
  ⟨fun z => FirstHalfFixedOutput.family (z.1, input u a ha ha1 hr z.2),
    FirstHalfFixedOutput.family.continuous.comp
      (continuous_fst.prodMk ((input u a ha ha1 hr).continuous.comp continuous_snd))⟩

theorem tested_fixed {r : ℝ} (hr : r ≤ 1) (s : _root_.unitInterval) (z : domain u a ha ha1 r) :
    (family u a ha ha1 hr (s, z)).1 = left (input u a ha ha1 hr z).val.1 :=
  FirstHalfFixedOutput.tested_fixed s (input u a ha ha1 hr z)

theorem family_zero {r : ℝ} (hr : r ≤ 1) (z : domain u a ha ha1 r) :
    family u a ha ha1 hr (0, z) =
      (left (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z)),
        right (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z))) :=
  FirstHalfFixedOutput.family_zero (input u a ha ha1 hr z)

theorem family_one {r : ℝ} (hr : r ≤ 1) (z : domain u a ha ha1 r) :
    family u a ha ha1 hr (1, z) =
      (left (input u a ha ha1 hr z).val.1,
        H1LoopJoin.join (1 / 2) (by norm_num) (by norm_num)
          (right (input u a ha ha1 hr z).val.1) (u z.val.2).val.2
          ((basepoint_right (input u a ha ha1 hr z).val.1).trans (u z.val.2).property)) :=
  FirstHalfFixedOutput.family_one (input u a ha ha1 hr z)

theorem retained_length {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n)
    (s : _root_.unitInterval) (z : domain u a ha ha1 r) :
    SobolevLength.length F (family u a ha ha1 hr (s, z)).2 =
      SobolevLength.length F (right (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z))) :=
  FirstHalfFixedOutput.length_original F s (input u a ha ha1 hr z)

def filteredDomain {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) : Set (domain u a ha ha1 r) :=
  {z | SobolevLength.length F (right (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z))) < A}

def filteredFamily {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    C(_root_.unitInterval × filteredDomain u a ha ha1 hr F A,
      {w : SphereLoop n | SobolevLength.length F w < A}) := by
  refine ⟨fun z => ⟨(family u a ha ha1 hr (z.1, z.2.val)).2, ?_⟩, ?_⟩
  · change SobolevLength.length F (family u a ha ha1 hr (z.1, z.2.val)).2 < A
    rw [retained_length]
    exact z.2.property
  · exact (continuous_snd.comp ((family u a ha ha1 hr).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

end
end Finsler.FirstHalfInteriorFamily
