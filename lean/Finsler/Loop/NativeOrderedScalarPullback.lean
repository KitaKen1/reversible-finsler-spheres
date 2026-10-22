module

public import Finsler.Loop.MultiFarPreimagePullback
public import Finsler.Loop.NativeOrderedDoubleCapCommon

/-! Pull back the SAME original Stage95 ordered input to any actual
source. Its difference from the genuine inverse-image common cap is
an explicit boundary. The complete primitive is zero on the inverse
image of the actual diagonal. All genuine GH tests are retained. -/
@[expose] public section
namespace Finsler.NativeOrderedScalarPullback
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeOrderedDoubleCapCommon
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

abbrev farFamily := DoubleFarCupOneCap.far (source m) (firstFar m hm F) (lastFar m hm F)
abbrev nearSet := firstNear m hm F ∩ lastNear m hm F

theorem far_open : ∀ i, IsOpen (farFamily m hm F i) :=
  DoubleFarCupOneCap.far_open (source m) (firstFar m hm F) (lastFar m hm F)
    (NativeOrderedDoubleCutSupported.far_open (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
      (NativeOrderedDoubleCutSupported.thomRadius m hm F))
    (NativeOrderedDoubleCutSupported.far_open (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
      (NativeOrderedDoubleCutSupported.thomRadius m hm F))

theorem near_open : IsOpen (nearSet m hm F) :=
  (NativeOrderedDoubleCutSupported.near_open (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
    (NativeClosingArcPowerVanishing.radius m hm F)).inter
  (NativeOrderedDoubleCutSupported.near_open (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
    (NativeClosingArcPowerVanishing.radius m hm F))

theorem cover : (⋃ i, farFamily m hm F i) ∪ nearSet m hm F = Set.univ :=
  DoubleFarCupOneCap.common_cover (source m) (firstFar m hm F) (firstNear m hm F)
    (lastFar m hm F) (lastNear m hm F)
    (NativeOrderedDoubleCutSupported.cover (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
      (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
    (NativeOrderedDoubleCutSupported.cover (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
      (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))

def thomCup := DoubleFarCupOneCap.leftCup (source m) (m + 1) m (firstThom m hm F) (lastThom m hm F)

theorem thomCup_supported : ∀ i, cochainPullback (SupportedCap.subspaceMap (source m) (farFamily m hm F i))
    ((m + 1) + m + 1) (thomCup m hm F) = 0 :=
  DoubleFarCupOneCap.left_supported (source m) (firstFar m hm F) (lastFar m hm F)
    (m + 1) m (firstThom m hm F) (lastThom m hm F) (first_supported m hm F) (last_supported m hm F)

theorem thomCup_closed : cochainCoboundary (ZMod 2) (source m) ((m + 1) + m + 1) (thomCup m hm F) = 0 :=
  CupCapOrder.closed (source m) (m + 1) (m + 1) ((m + 1) + m + 1) (by omega)
    (firstThom m hm F) (lastThom m hm F)
    (NativeOrderedDoubleCutSupported.thom_closed (NativeOrderedDoubleCutGeometry.firstParameter (m + 1))
      (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
    (NativeOrderedDoubleCutSupported.thom_closed (NativeOrderedDoubleCutGeometry.lastParameter (m + 1))
      (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))

variable {X : TopCat.{0}} (f : X ⟶ source m) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def localValue : singularCochainGroup (ZMod 2) X (index m a b k + 1) :=
  MultiFarPreimagePullback.localValue f (farFamily m hm F) (nearSet m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
    (thomCup m hm F) (thomCup_supported m hm F) (test m hm F a b k E)

def pullbackPrimitive : singularCochainGroup (ZMod 2) X (index m a b k) :=
  MultiFarPreimagePullback.primitive f (farFamily m hm F) (nearSet m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
    (thomCup m hm F) (thomCup_supported m hm F) (test m hm F a b k E)

theorem local_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) X (index m a b k) (pullbackPrimitive m hm F f a b k E) =
      localValue m hm F f a b k E - cochainPullback f (index m a b k + 1) (coupled m hm F a b k E) :=
  MultiFarPreimagePullback.boundary f (farFamily m hm F) (nearSet m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
    (thomCup m hm F) (thomCup_supported m hm F) (test m hm F a b k E)
    (thomCup_closed m hm F) (test_closed m hm F a b k E hE)

def primitive : singularCochainGroup (ZMod 2) X (index m a b k) :=
  cochainPullback f (index m a b k) (NativeOrderedDoubleCapCommon.primitive m hm F a b k E) -
    pullbackPrimitive m hm F f a b k E

private theorem pullback_sub {X Y : TopCat.{0}} (g : X ⟶ Y) (n : ℕ)
    (A B : singularCochainGroup (ZMod 2) Y n) :
    cochainPullback g n (A - B) = cochainPullback g n A - cochainPullback g n B :=
  map_sub ((singularCochainComplexZMod2.map g.op).f n).hom A B

theorem original_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) X (index m a b k) (primitive m hm F f a b k E) =
      cochainPullback f (index m a b k + 1)
        (CochainDegreeTransport.pre (source m) (degree_match m a b k)
          (NativeOrderedDoubleCutSupported.cochain m hm F a b k E)) - localValue m hm F f a b k E := by
  have hp := SmallChainPrimitiveCorrection.pullback_boundary f (index m a b k) (index m a b k + 1)
    (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)
  change cochainCoboundary (ZMod 2) X (index m a b k)
      (cochainPullback f (index m a b k) (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)) =
    cochainPullback f (index m a b k + 1)
      (cochainCoboundary (ZMod 2) (source m) (index m a b k)
        (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)) at hp
  rw [NativeOrderedDoubleCapCommon.original_boundary m hm F a b k E hE, pullback_sub] at hp
  change ((cochainCxZMod2 X).d (index m a b k) (index m a b k + 1)).hom
    (cochainPullback f (index m a b k) (NativeOrderedDoubleCapCommon.primitive m hm F a b k E) -
      pullbackPrimitive m hm F f a b k E) = _
  rw [map_sub]
  change cochainCoboundary (ZMod 2) X (index m a b k)
      (cochainPullback f (index m a b k) (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)) -
    cochainCoboundary (ZMod 2) X (index m a b k) (pullbackPrimitive m hm F f a b k E) = _
  rw [hp, local_boundary m hm F f a b k E hE]
  abel

theorem primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap X (f ⁻¹' NativeOrderedDoubleCutSupported.diagonal m)) (index m a b k)
      (primitive m hm F f a b k E) = 0 := by
  have hp := pullback_support f (f ⁻¹' NativeOrderedDoubleCutSupported.diagonal m)
    (NativeOrderedDoubleCutSupported.diagonal m) (fun _ h => h) (index m a b k)
    (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)
    (NativeOrderedDoubleCapCommon.primitive_diagonal_zero m hm F a b k E)
  have hq := MultiFarPreimagePullback.primitive_zero f (farFamily m hm F) (nearSet m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
    (thomCup m hm F) (thomCup_supported m hm F) (test m hm F a b k E)
    (NativeOrderedDoubleCutSupported.diagonal m) (diagonal_test_zero m hm F a b k E)
  unfold primitive
  rw [pullback_sub, hp]
  exact sub_eq_zero.mpr hq.symm

theorem relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains X).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (f ⁻¹' NativeOrderedDoubleCutSupported.diagonal m))).X (index m a b k))
    (hc : c ≫ (chains X).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap X (f ⁻¹' NativeOrderedDoubleCutSupported.diagonal m))).f (index m a b k)) :
    c ≫ cochainPullback f (index m a b k + 1)
        (CochainDegreeTransport.pre (source m) (degree_match m a b k)
          (NativeOrderedDoubleCutSupported.cochain m hm F a b k E)) = c ≫ localValue m hm F f a b k E := by
  have hb := congrArg (fun a => c ≫ a) (original_boundary m hm F f a b k E hE)
  have hz : (push (SupportedCap.subspaceMap X (f ⁻¹' NativeOrderedDoubleCutSupported.diagonal m))).f
      (index m a b k) ≫ primitive m hm F f a b k E = 0 := primitive_diagonal_zero m hm F f a b k E
  change c ≫ ((chains X).d (index m a b k + 1) (index m a b k) ≫ primitive m hm F f a b k E) = _ at hb
  rw [← Category.assoc, hc, Category.assoc, hz, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.NativeOrderedScalarPullback
