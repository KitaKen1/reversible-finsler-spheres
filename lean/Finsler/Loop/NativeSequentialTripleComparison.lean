module

public import Finsler.Loop.NativeSequentialPrefixMiddle
public import Finsler.Loop.NativeSequentialSuffixMiddle
public import Finsler.Topology.DiagonalCohomology

/-! BOTH original sequential output TRIPLES are homotopic to the SAME
common three actual H1 loops on the positive-split domains. The first
and last outputs stay fixed and each middle length stays exactly fixed.
Consequently EVERY genuine cohomology test on the triple pulls back
equally. The missing seams/collars and supported-cap comparison remain
separate; this is not a substitute definition of the original cut. -/
@[expose] public section
namespace Finsler.NativeSequentialTripleComparison
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.NativeSequentialCutParameters
open Finsler.NativeSequentialCutOuterOutputs Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {n : ℕ} {r : ℝ}

abbrev triple (n : ℕ) := TopCat.of (SphereLoop n × SphereLoop n × SphereLoop n)

def commonTriple (hr : r ≤ 1) : NativeOrderedDoubleCutGeometry.domain n r ⟶ triple n := TopCat.ofHom
  ⟨fun z => (left (NativeOrderedDoubleCutGeometry.firstCut hr z),
    NativeOrderedDoubleCutGeometry.middle hr z, right (NativeOrderedDoubleCutGeometry.lastCut hr z)),
    ((continuous_left (n := n)).comp (NativeOrderedDoubleCutGeometry.continuous_firstCut hr)).prodMk
      ((NativeOrderedDoubleCutGeometry.continuous_middle hr).prodMk
        ((continuous_right (n := n)).comp (NativeOrderedDoubleCutGeometry.continuous_lastCut hr)))⟩

def prefixOriginal (hr : r ≤ 1) : TopCat.of (NativeSequentialPrefixMiddle.inputs n r) ⟶ triple n := TopCat.ofHom
  ⟨fun z => (left (prefixInner hr z.val), right (prefixInner hr z.val), right z.val.val.1), by
    have hi : Continuous (fun z : NativeSequentialPrefixMiddle.inputs n r => prefixInner hr z.val) :=
      (continuous_prefixInner hr).comp continuous_subtype_val
    have ho : Continuous (fun z : NativeSequentialPrefixMiddle.inputs n r => z.val.val.1) := by fun_prop
    exact ((continuous_left (n := n)).comp hi).prodMk
      (((continuous_right (n := n)).comp hi).prodMk ((continuous_right (n := n)).comp ho))⟩

def suffixOriginal (hr : r ≤ 1) : TopCat.of (NativeSequentialSuffixMiddle.inputs n r) ⟶ triple n := TopCat.ofHom
  ⟨fun z => (left z.val.val.1, left (suffixInner hr z.val), right (suffixInner hr z.val)), by
    have hi : Continuous (fun z : NativeSequentialSuffixMiddle.inputs n r => suffixInner hr z.val) :=
      (continuous_suffixInner hr).comp continuous_subtype_val
    have ho : Continuous (fun z : NativeSequentialSuffixMiddle.inputs n r => z.val.val.1) := by fun_prop
    exact ((continuous_left (n := n)).comp ho).prodMk
      (((continuous_left (n := n)).comp hi).prodMk ((continuous_right (n := n)).comp hi))⟩

def prefixCommonTriple (hr : r ≤ 1) : TopCat.of (NativeSequentialPrefixMiddle.inputs n r) ⟶ triple n :=
  TopCat.ofHom ⟨fun z => commonTriple hr (prefixCommon z.val),
    (commonTriple hr).hom.continuous.comp (continuous_prefixCommon.comp continuous_subtype_val)⟩

def suffixCommonTriple (hr : r ≤ 1) : TopCat.of (NativeSequentialSuffixMiddle.inputs n r) ⟶ triple n :=
  TopCat.ofHom ⟨fun z => commonTriple hr (suffixCommon z.val),
    (commonTriple hr).hom.continuous.comp (continuous_suffixCommon.comp continuous_subtype_val)⟩

def prefixHomotopy (hr : r ≤ 1) : TopCat.Homotopy (prefixOriginal (n := n) hr) (prefixCommonTriple hr) where
  toFun z := ((prefixCommonTriple hr z.2).1,
    NativeSequentialPrefixMiddle.homotopy hr (z.1, z.2), (prefixCommonTriple hr z.2).2.2)
  continuous_toFun := by
    have hc := (prefixCommonTriple hr).hom.continuous.comp
      (continuous_snd (X := _root_.unitInterval) (Y := NativeSequentialPrefixMiddle.inputs n r))
    exact (continuous_fst.comp hc).prodMk
      ((NativeSequentialPrefixMiddle.homotopy hr).continuous.prodMk (continuous_snd.comp (continuous_snd.comp hc)))
  map_zero_left z := Prod.ext (prefix_common_first hr z.val).symm
    (Prod.ext ((NativeSequentialPrefixMiddle.homotopy hr).map_zero_left z)
      (prefix_common_last hr z.val).symm)
  map_one_left z := Prod.ext rfl (Prod.ext ((NativeSequentialPrefixMiddle.homotopy hr).map_one_left z) rfl)

def suffixHomotopy (hr : r ≤ 1) : TopCat.Homotopy (suffixOriginal (n := n) hr) (suffixCommonTriple hr) where
  toFun z := ((suffixCommonTriple hr z.2).1,
    NativeSequentialSuffixMiddle.homotopy hr (z.1, z.2), (suffixCommonTriple hr z.2).2.2)
  continuous_toFun := by
    have hc := (suffixCommonTriple hr).hom.continuous.comp
      (continuous_snd (X := _root_.unitInterval) (Y := NativeSequentialSuffixMiddle.inputs n r))
    exact (continuous_fst.comp hc).prodMk
      ((NativeSequentialSuffixMiddle.homotopy hr).continuous.prodMk (continuous_snd.comp (continuous_snd.comp hc)))
  map_zero_left z := Prod.ext (suffix_common_first hr z.val).symm
    (Prod.ext ((NativeSequentialSuffixMiddle.homotopy hr).map_zero_left z)
      (suffix_common_last hr z.val).symm)
  map_one_left z := Prod.ext rfl (Prod.ext ((NativeSequentialSuffixMiddle.homotopy hr).map_one_left z) rfl)

theorem prefix_pullback (hr : r ≤ 1) (q : ℕ) (T : cohomologyZMod2 (triple n) q) :
    (cohPullback (prefixOriginal hr) q).hom T = (cohPullback (prefixCommonTriple hr) q).hom T :=
  DiagonalCohomology.homotopy_pullback (prefixHomotopy hr) q T

theorem suffix_pullback (hr : r ≤ 1) (q : ℕ) (T : cohomologyZMod2 (triple n) q) :
    (cohPullback (suffixOriginal hr) q).hom T = (cohPullback (suffixCommonTriple hr) q).hom T :=
  DiagonalCohomology.homotopy_pullback (suffixHomotopy hr) q T

theorem prefix_middle_length (hr : r ≤ 1) (F : ReversibleMetric n) (s : _root_.unitInterval)
    (z : NativeSequentialPrefixMiddle.inputs n r) :
    SobolevLength.length F ((prefixHomotopy hr) (s, z)).2.1 =
      SobolevLength.length F (prefixCommonTriple hr z).2.1 :=
  NativeSequentialPrefixMiddle.homotopy_length hr F s z

theorem suffix_middle_length (hr : r ≤ 1) (F : ReversibleMetric n) (s : _root_.unitInterval)
    (z : NativeSequentialSuffixMiddle.inputs n r) :
    SobolevLength.length F ((suffixHomotopy hr) (s, z)).2.1 =
      SobolevLength.length F (suffixCommonTriple hr z).2.1 :=
  NativeSequentialSuffixMiddle.homotopy_length hr F s z

end
end Finsler.NativeSequentialTripleComparison
