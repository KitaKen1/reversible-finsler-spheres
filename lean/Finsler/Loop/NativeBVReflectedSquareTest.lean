module

public import Finsler.Loop.ComplementRotationShearCochain
public import Finsler.Loop.NativeBVComplementCapTest

/-! Every SAME original BV coefficient is the reflected-cut square
value of the original normalized Thom/evaluation/GH test. The shear
is removed by its actual periodic-face primitive, not by a BV law. -/
@[expose] public section
namespace Finsler.NativeBVReflectedSquareTest
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily
open Finsler.NativeInnerCutPullback Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (T : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h T) =
      CochainDegreeTransport.pre X h (cochainPullback f j T) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

private theorem aligned_diagonal (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1)))
      (m + q + 1) (GlobalThomTime.aligned m hρ hρr q ≫ K) = 0 := by
  have hz : (push (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1)))).f
      (m + q + 1) ≫ GlobalThomTime.aligned m hρ hρr q = 0 :=
    SupportedThomTime.endpoint (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _)
      (cover _ hρr) m (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
      (NormalizedSelfCut.cocycle_supported _ _ hρ) (NormalizedSelfCut.cocycle_closed _ _ hρ)
      (SupportedCap.subspaceMap _ _) (FilteredGlobalThomTime.endpointCarrier (m + 1))
      (FilteredGlobalThomTime.cocycle_endpoint m hρ) (fun z => z.property) q
  change (push (SupportedCap.subspaceMap _ _)).f _ ≫ (_ ≫ K) = 0
  rw [← Category.assoc, hz, zero_comp]

private theorem double_prism_at (n q k : ℕ) (h : q + 1 = k)
    (T : singularCochainGroup (ZMod 2) (parameters n) (k + 1)) :
    (H1LoopRotation.chainHomotopy n).hom q (q + 1) ≫
      CochainDegreeTransport.pre _ h (SelfCutTimePrism.prism n k ≫
        cochainPullback (WholeSelfCutComplement.complement n) (k + 1) T) =
    NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (NativeBVRotationSquare.intoCut n ≫ WholeSelfCutComplement.complement n) (q + 2)
        (CochainDegreeTransport.pre _ (congrArg (fun a => a + 1) h) T) := by
  subst k
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]
  rw [pullback_comp]
  change _ ≫ (_ ≫ _) = _ ≫ ((push (NativeBVRotationSquare.intoCut n)).f (q + 2) ≫ _)
  rw [← Category.assoc, NativeBVRotationSquare.double_prism, Category.assoc]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def parameter : singularCochainGroup (ZMod 2) (parameters (m + 1)) (NativeGHPowers.degree m (r + 1) + 2) :=
  CochainDegreeTransport.pre _ (by have := NativeBVReorderedTest.degree_match m r; omega)
    (GlobalThomTime.aligned m (rhoPos m hm F) (rhoLt m hm F) (NativeGHPowers.degree m r + m + 1) ≫
      NativeBVComplementCapTest.near m hm F r)

theorem parameter_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1) + 2)
    (parameter m hm F r) = 0 := by
  apply CochainDegreeTransport.closed
  have he := congrArg (fun f => f ≫ NativeBVComplementCapTest.near m hm F r)
    (GlobalThomTime.comm m (rhoPos m hm F) (rhoLt m hm F) (NativeGHPowers.degree m r + m + 1))
  have hz := NativeBVComplementCapTest.near_closed m hm F r
  change (chains _).d _ _ ≫ NativeBVComplementCapTest.near m hm F r = 0 at hz
  change (chains _).d _ _ ≫ (_ ≫ NativeBVComplementCapTest.near m hm F r) = 0
  simpa only [Nat.add_assoc, Category.assoc, hz, comp_zero] using he.symm

theorem parameter_diagonal_zero :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1)))
      (NativeGHPowers.degree m (r + 1) + 2) (parameter m hm F r) = 0 := by
  unfold parameter
  rw [pullback_pre, aligned_diagonal]
  exact comp_zero

def test : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  NativeGlobalTimeSquare.squarePrism (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) ≫
    cochainPullback (ComplementRotationShear.reflected (m + 1)) (NativeGHPowers.degree m (r + 1) + 2)
      (parameter m hm F r)

def primitive : singularCochainGroup (ZMod 2) (NativeBVRotationSquare.squareDomain (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) :=
  ComplementRotationShearCochain.primitive (m + 1) (NativeGHPowers.degree m (r + 1)) (parameter m hm F r)

theorem primitive_boundary : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1) + 1)
    (primitive m hm F r) =
      cochainPullback (ComplementRotationShear.reflected (m + 1)) (NativeGHPowers.degree m (r + 1) + 2)
        (parameter m hm F r) -
      cochainPullback (NativeBVRotationSquare.intoCut (m + 1) ≫ WholeSelfCutComplement.complement (m + 1))
        (NativeGHPowers.degree m (r + 1) + 2) (parameter m hm F r) :=
  ComplementRotationShearCochain.boundary _ _ _ (parameter_closed m hm F r)

theorem primitive_cut_zero (t : _root_.unitInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (DoubleRelativeTimeCylinder.atTime (NativeBVRotationSquare.rotationDomain (m + 1)) t)
      (NativeGHPowers.degree m (r + 1) + 1) (primitive m hm F r) = 0 :=
  ComplementRotationShearCochain.cut_zero _ _ _ (parameter_diagonal_zero m hm F r) t ht

theorem primitive_rotation_equal :
    cochainPullback (NativeBVRotationSquare.rotationFace (m + 1) 0) (NativeGHPowers.degree m (r + 1) + 1)
      (primitive m hm F r) =
    cochainPullback (NativeBVRotationSquare.rotationFace (m + 1) 1) (NativeGHPowers.degree m (r + 1) + 1)
      (primitive m hm F r) := ComplementRotationShearCochain.rotation_equal _ _ _

theorem complemented_square :
    SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVComplementCapTest.test m hm F r) =
      NativeGlobalTimeSquare.squarePrism (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) ≫
        cochainPullback (NativeBVRotationSquare.intoCut (m + 1) ≫ WholeSelfCutComplement.complement (m + 1))
          (NativeGHPowers.degree m (r + 1) + 2) (parameter m hm F r) :=
  double_prism_at (m + 1) (NativeGHPowers.degree m (r + 1)) (m + (NativeGHPowers.degree m r + m + 1))
    (by have := NativeBVReorderedTest.degree_match m r; omega) _

theorem cycle_values :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVComplementCapTest.test m hm F r) := by
  rw [complemented_square]
  exact ComplementRotationShearCochain.square_values _ _ _ (parameter_closed m hm F r) (parameter_diagonal_zero m hm F r)

theorem coefficient_on_cycle (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    NativeBVOriginalScalar.coefficient m hm P v₀ r =
      ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r).hom c := by
  rw [cycle_values]
  exact NativeBVComplementCapTest.coefficient_on_cycle m hm F r P v₀ c hc

end
end Finsler.NativeBVReflectedSquareTest
