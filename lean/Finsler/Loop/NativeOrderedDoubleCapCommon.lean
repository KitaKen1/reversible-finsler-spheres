module

public import Finsler.Loop.OriginalDoubleCapCommonComparison
public import Finsler.Loop.NativeOrderedDoubleCutSupported
public import Finsler.Loop.NativeSuffixPostponedAlignment
public import Finsler.Loop.OriginalDoubleCapCarrier

/-! The same ORIGINAL ordered-loop source, original normalized Thom
cochains and genuine GH output tests instantiate the three-open-cover
comparison. The explicit boundary keeps both actual supported cuts.
This is the first-then-last common geometry; the opposite order and
the complete original sequential time insertion remain separate. -/
@[expose] public section
namespace Finsler.NativeOrderedDoubleCapCommon
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev source := NativeOrderedDoubleCutGeometry.source (m + 1)
abbrev firstFar := NativeOrderedDoubleCutSupported.far (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev firstNear := NativeOrderedDoubleCutSupported.near (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
  (NativeClosingArcPowerVanishing.radius m hm F)
abbrev lastFar := NativeOrderedDoubleCutSupported.far (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev lastNear := NativeOrderedDoubleCutSupported.near (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
  (NativeClosingArcPowerVanishing.radius m hm F)

def firstThom := NativeOrderedDoubleCutSupported.thom (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
  (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
def lastThom := NativeOrderedDoubleCutSupported.thom (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
  (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)

theorem first_supported : cochainPullback (SupportedCap.subspaceMap (source m) (firstFar m hm F)) _
    (firstThom m hm F) = 0 := NativeOrderedDoubleCutSupported.thom_supported _ _ _
theorem last_supported : cochainPullback (SupportedCap.subspaceMap (source m) (lastFar m hm F)) _
    (lastThom m hm F) = 0 := NativeOrderedDoubleCutSupported.thom_supported _ _ _

def joint : TopCat.of (firstNear m hm F ∩ lastNear m hm F : Set (source m)) ⟶
    NativeOrderedDoubleCutCochain.domain m hm F := TopCat.ofHom
  ⟨fun z => ⟨z.val, z.property.1, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)
abbrev testDegree := NativeOrderedDoubleCutSupported.testDegree m a b k
abbrev index := ((m + 1) + m) + testDegree m a b k

def test : singularCochainGroup (ZMod 2)
    (TopCat.of (firstNear m hm F ∩ lastNear m hm F : Set (source m))) (testDegree m a b k) :=
  cochainPullback (joint m hm F) _ (NativeOrderedDoubleCutCochain.tests m hm F a b k E)

theorem test_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (test m hm F a b k E) = 0 :=
  pullback_closed _ _ _ (NativeOrderedDoubleCutCochain.tests_closed m hm F a b k E hE)

def sequential := OriginalDoubleCapCommonComparison.sequential (source m)
  (firstFar m hm F) (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (firstThom m hm F) (lastThom m hm F)
  (first_supported m hm F) (last_supported m hm F) (test m hm F a b k E)

def coupled := OriginalDoubleCapCommonComparison.coupled (source m)
  (firstFar m hm F) (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (firstThom m hm F) (lastThom m hm F)
  (first_supported m hm F) (last_supported m hm F) (test m hm F a b k E)

def primitive := OriginalDoubleCapCommonComparison.primitive (source m)
  (firstFar m hm F) (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (firstThom m hm F) (lastThom m hm F)
  (first_supported m hm F) (last_supported m hm F) (test m hm F a b k E)

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source m) (index m a b k) (primitive m hm F a b k E) =
      sequential m hm F a b k E - coupled m hm F a b k E :=
  OriginalDoubleCapCommonComparison.boundary (source m)
    (firstFar m hm F) (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (m + 1) m (testDegree m a b k) (firstThom m hm F) (lastThom m hm F)
    (first_supported m hm F) (last_supported m hm F) (test m hm F a b k E)
    (NativeOrderedDoubleCutSupported.thom_closed _ _ _) (NativeOrderedDoubleCutSupported.thom_closed _ _ _)
    (test_closed m hm F a b k E hE)

theorem degree_match : index m a b k + 1 = NativeOrderedDoubleCutSupported.totalDegree m a b k := by
  dsimp [index, testDegree, NativeOrderedDoubleCutSupported.totalDegree]
  omega

set_option maxHeartbeats 180000 in
theorem inner_eq : OriginalDoubleSupportedCap.inner (source m)
    (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
    (NativeOrderedDoubleCutSupported.far_open (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
      (NativeOrderedDoubleCutSupported.thomRadius m hm F)) (NativeOrderedDoubleCutSupported.near_open (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
      (NativeClosingArcPowerVanishing.radius m hm F))
    (NativeOrderedDoubleCutSupported.cover (NativeOrderedDoubleCutGeometry.lastParameter (m + 1)) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (m + 1) (testDegree m a b k) (lastThom m hm F) (last_supported m hm F) (test m hm F a b k E) =
      NativeOrderedDoubleCutSupported.secondCochain m hm F a b k E := by
  let Y := NativeOrderedDoubleCutSupported.firstSpace m hm F
  let A := OriginalDoubleSupportedCap.secondFar (source m) (firstNear m hm F) (lastFar m hm F)
  let B := OriginalDoubleSupportedCap.secondNear (source m) (firstNear m hm F) (lastNear m hm F)
  let j := SupportedCap.subspaceMap (source m) (firstNear m hm F)
  have he : cochainPullback j (m + 1) (lastThom m hm F) =
      NativeOrderedDoubleCutSupported.thom (NativeOrderedDoubleCutSupported.secondParameter m hm F)
        (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) := by
    change cochainPullback j (m + 1)
      (cochainPullback (NativeOrderedDoubleCutGeometry.lastParameter (m + 1)) (m + 1)
        (NormalizedSelfCut.cocycle (m + 1) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))) =
      cochainPullback (j ≫ NativeOrderedDoubleCutGeometry.lastParameter (m + 1)) (m + 1)
        (NormalizedSelfCut.cocycle (m + 1) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
    exact (pullback_comp _ _ _ _).symm
  have hc := SupportedCapCochainCongruence.cut_eq Y
    (NativeOrderedDoubleCutSupported.far (NativeOrderedDoubleCutSupported.secondParameter m hm F)
      (NativeOrderedDoubleCutSupported.thomRadius m hm F))
    (NativeOrderedDoubleCutSupported.near (NativeOrderedDoubleCutSupported.secondParameter m hm F)
      (NativeClosingArcPowerVanishing.radius m hm F))
    (NativeOrderedDoubleCutSupported.far_open (NativeOrderedDoubleCutSupported.secondParameter m hm F)
      (NativeOrderedDoubleCutSupported.thomRadius m hm F))
    (NativeOrderedDoubleCutSupported.near_open (NativeOrderedDoubleCutSupported.secondParameter m hm F)
      (NativeClosingArcPowerVanishing.radius m hm F))
    (NativeOrderedDoubleCutSupported.cover (NativeOrderedDoubleCutSupported.secondParameter m hm F)
      (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (m + 1) (testDegree m a b k) ((m + 1) + testDegree m a b k) rfl
    (cochainPullback j (m + 1) (lastThom m hm F))
    (NativeOrderedDoubleCutSupported.thom (NativeOrderedDoubleCutSupported.secondParameter m hm F)
      (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
    (pullback_support j A (lastFar m hm F) (fun _ h => h) (m + 1) (lastThom m hm F) (last_supported m hm F))
    (NativeOrderedDoubleCutSupported.thom_supported (NativeOrderedDoubleCutSupported.secondParameter m hm F)
      (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) he
  have hj : OriginalDoubleSupportedCap.jointMap (source m) (firstNear m hm F) (lastNear m hm F) ≫ joint m hm F =
      NativeOrderedDoubleCutSupported.jointMap m hm F := by rfl
  have hp : cochainPullback (OriginalDoubleSupportedCap.jointMap (source m) (firstNear m hm F) (lastNear m hm F))
      (testDegree m a b k) (test m hm F a b k E) =
      cochainPullback (NativeOrderedDoubleCutSupported.jointMap m hm F) _
        (NativeOrderedDoubleCutCochain.tests m hm F a b k E) := by
    rw [test, ← pullback_comp, hj]
  unfold OriginalDoubleSupportedCap.inner NativeOrderedDoubleCutSupported.secondCochain
  rw [hp]
  exact congrArg (fun c => c ≫ cochainPullback (NativeOrderedDoubleCutSupported.jointMap m hm F)
    (testDegree m a b k) (NativeOrderedDoubleCutCochain.tests m hm F a b k E)) hc

theorem stage95_compare : CochainDegreeTransport.pre (source m) (degree_match m a b k)
    (NativeOrderedDoubleCutSupported.cochain m hm F a b k E) = sequential m hm F a b k E := by
  have h := NativeSuffixPostponedAlignment.pre_cut (source m) (firstFar m hm F) (firstNear m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (m + 1) ((m + 1) + testDegree m a b k) (index m a b k + 1)
    (NativeOrderedDoubleCutSupported.totalDegree m a b k)
    (by dsimp [index]; omega) rfl (degree_match m a b k) (firstThom m hm F) (first_supported m hm F)
    (NativeOrderedDoubleCutSupported.secondCochain m hm F a b k E)
  change CochainDegreeTransport.pre (source m) (degree_match m a b k)
    (NativeOrderedDoubleCutSupported.cochain m hm F a b k E) =
      SupportedCap.cut (source m) (firstFar m hm F) (firstNear m hm F)
        (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
        (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
        (m + 1) ((m + 1) + testDegree m a b k) (index m a b k + 1) (by dsimp [index]; omega)
        (firstThom m hm F) (first_supported m hm F) ≫
          NativeOrderedDoubleCutSupported.secondCochain m hm F a b k E at h
  exact h.trans (congrArg (fun T => SupportedCap.cut (source m) (firstFar m hm F) (firstNear m hm F)
      (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
      (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
      (m + 1) ((m + 1) + testDegree m a b k) (index m a b k + 1) (by dsimp [index]; omega)
      (firstThom m hm F) (first_supported m hm F) ≫ T) (inner_eq m hm F a b k E).symm)

theorem diagonal_test_zero : cochainPullback
    (restriction (SupportedCap.subspaceMap (source m) (NativeOrderedDoubleCutSupported.diagonal m))
      ((SupportedCap.subspaceMap (source m) (NativeOrderedDoubleCutSupported.diagonal m)) ⁻¹'
        (firstNear m hm F ∩ lastNear m hm F)) (firstNear m hm F ∩ lastNear m hm F) (fun _ h => h))
    (testDegree m a b k) (test m hm F a b k E) = 0 := by
  let S := NativeOrderedDoubleCutSupported.diagonal m
  let f := restriction (SupportedCap.subspaceMap (source m) S)
    ((SupportedCap.subspaceMap (source m) S) ⁻¹' (firstNear m hm F ∩ lastNear m hm F))
    (firstNear m hm F ∩ lastNear m hm F) (fun _ h => h)
  let d : TopCat.of ((SupportedCap.subspaceMap (source m) S) ⁻¹' (firstNear m hm F ∩ lastNear m hm F)) ⟶
      NativeOrderedDoubleCutDiagonal.diagonalDomain (m + 1) (NativeClosingArcPowerVanishing.radius m hm F) :=
    TopCat.ofHom ⟨fun z => ⟨joint m hm F (f z), z.val.property⟩,
      ((joint m hm F).hom.continuous.comp f.hom.continuous).subtype_mk _⟩
  have he : f ≫ joint m hm F = d ≫ NativeOrderedDoubleCutDiagonal.inclusion (m + 1)
      (NativeClosingArcPowerVanishing.radius m hm F) := rfl
  change cochainPullback f _ (test m hm F a b k E) = 0
  rw [test, ← pullback_comp, he, pullback_comp, NativeOrderedDoubleCutCochain.tests_diagonal_zero]
  change (push d).f _ ≫ 0 = 0
  exact comp_zero

theorem primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source m) (NativeOrderedDoubleCutSupported.diagonal m)) _
    (primitive m hm F a b k E) = 0 :=
  OriginalDoubleCapCarrier.primitive_zero (source m)
    (firstFar m hm F) (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (m + 1) m (testDegree m a b k) (firstThom m hm F) (lastThom m hm F)
    (first_supported m hm F) (last_supported m hm F) (test m hm F a b k E)
    (NativeOrderedDoubleCutSupported.diagonal m) (diagonal_test_zero m hm F a b k E)

theorem original_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source m) (index m a b k) (primitive m hm F a b k E) =
      CochainDegreeTransport.pre (source m) (degree_match m a b k)
        (NativeOrderedDoubleCutSupported.cochain m hm F a b k E) - coupled m hm F a b k E := by
  rw [stage95_compare]
  exact boundary m hm F a b k E hE

theorem coupled_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source m) (index m a b k + 1) (coupled m hm F a b k E) = 0 :=
  DoubleFarCupOneCap.left_closed (source m) (firstFar m hm F) (lastFar m hm F)
    (m + 1) m (firstThom m hm F) (lastThom m hm F) (first_supported m hm F) (last_supported m hm F)
    (firstNear m hm F ∩ lastNear m hm F)
    (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
    ((NativeOrderedDoubleCutSupported.near_open _ _).inter (NativeOrderedDoubleCutSupported.near_open _ _))
    (DoubleFarCupOneCap.common_cover (source m) (firstFar m hm F) (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
      (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
      (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)))
    (testDegree m a b k) (test m hm F a b k E)
    (NativeOrderedDoubleCutSupported.thom_closed _ _ _) (NativeOrderedDoubleCutSupported.thom_closed _ _ _)
    (test_closed m hm F a b k E hE)

theorem class_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    CochainClass.classOf (cochainCxZMod2 (source m)) (index m a b k + 1)
      (CochainDegreeTransport.pre (source m) (degree_match m a b k)
        (NativeOrderedDoubleCutSupported.cochain m hm F a b k E))
      (CochainDegreeTransport.closed _ _ _ (NativeOrderedDoubleCutSupported.cochain_closed m hm F a b k E hE)) =
    CochainClass.classOf (cochainCxZMod2 (source m)) (index m a b k + 1) (coupled m hm F a b k E)
      (coupled_closed m hm F a b k E hE) := by
  apply RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 (source m)) (index m a b k) _
    (primitive m hm F a b k E)
  change _ - _ = cochainCoboundary (ZMod 2) (source m) _ (primitive m hm F a b k E)
  exact (original_boundary m hm F a b k E hE).symm

end
end Finsler.NativeOrderedDoubleCapCommon
