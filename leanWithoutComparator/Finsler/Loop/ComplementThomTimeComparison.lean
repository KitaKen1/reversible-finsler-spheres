module

public import Finsler.Loop.ComplementThomEndpointPrimitive
public import Finsler.Loop.SupportedThomTimeRepresentative
public import Finsler.Loop.GlobalTimeCupConstantsVanish

/-! The actual complemented Thom REPRESENTATIVE may now be replaced by
the original one AFTER the original cut-time insertion. Its explicit
neighborhood-valued correction has zero diagonal faces. The coordinate
change of subdivision under complement remains a separate comparison. -/
@[expose] public section
namespace Finsler.ComplementThomTimeComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.ComplementThomEndpointPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 1 ≤ m) {ρ r : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) (hρr : ρ < r)

def operation := SupportedThomTime.operation (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
  (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m (swapped m hρ)
  (swapped_supported m hρ) (swapped_closed m hρ)
  (atTime (m + 1) 0) (atTime (m + 1) 1) (SelfCutTimePrism.chainHomotopy (m + 1))
  (FilteredGlobalThomTime.endpointCarrier (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))
  (swapped_carrier_zero m hm hρ hρ2) (swapped_carrier_zero m hm hρ hρ2)
  (fun _ => rfl) (fun u => (sphereRepresentative_endpoints u).symm)

def primitiveCap (q : ℕ) := SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
  (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m q (m + q) rfl
  (primitive m hm hρ hρ2) (supported m hm hρ hρ2)

def upperCap (q : ℕ) := SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
  (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m (q + 1) (m + q + 1) (by omega)
  (primitive m hm hρ hρ2) (supported m hm hρ hρ2)

theorem cap_diagonal_zero (q : ℕ) {X : TopCat.{0}} (f : X ⟶ parameters (m + 1))
    (hf : ∀ x, f x ∈ FilteredGlobalThomTime.endpointCarrier (m + 1)) :
    (push f).f (m + q) ≫ primitiveCap m hm hρ hρ2 hρr q = 0 :=
  SelfCutEndpoints.cut_map_zero (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (FilteredGlobalThomTime.endpointCarrier (m + 1))
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m q
    (primitive m hm hρ hρ2) (supported m hm hρ hρ2) (carrier_zero m hm hρ hρ2) f hf

theorem cap_endpoint_zero (q : ℕ) (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    (push (atTime (m + 1) t)).f (m + q) ≫ primitiveCap m hm hρ hρ2 hρr q = 0 := by
  apply cap_diagonal_zero m hm hρ hρ2 hρr
  rcases ht with rfl | rfl
  · exact fun _ => rfl
  · exact fun u => (sphereRepresentative_endpoints u).symm

theorem cap_boundary (q : ℕ) :
    upperCap m hm hρ hρ2 hρr q ≫ (chains (TopCat.of (neighborhood (m + 1) r))).d (q + 1) q =
      (chains (parameters (m + 1))).d (m + q + 1) (m + q) ≫ primitiveCap m hm hρ hρ2 hρr q -
        (SupportedThomTime.aligned (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
          (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m (swapped m hρ)
          (swapped_supported m hρ) (swapped_closed m hρ) q - GlobalThomTime.aligned m hρ hρr q) :=
  SupportedThomTimeRepresentative.boundary (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m (swapped m hρ)
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) (swapped_supported m hρ)
    (NormalizedSelfCut.cocycle_supported _ _ hρ) (swapped_closed m hρ)
    (NormalizedSelfCut.cocycle_closed _ _ hρ) (primitive m hm hρ hρ2) (supported m hm hρ hρ2)
    (boundary m hm hρ hρ2) q

def timeCorrection (q : ℕ) :=
  -(SelfCutTimePrism.prism (m + 1) (m + q) ≫ upperCap m hm hρ hρ2 hρr q)

theorem cycle_boundary (q : ℕ) {M : ModuleCat.{0} (ZMod 2)}
    (z : M ⟶ (chains (TopCat.of (SphereLoop (m + 1)))).X (m + q))
    (hz : z ≫ (chains (TopCat.of (SphereLoop (m + 1)))).d (m + q) (m + q - 1) = 0) :
    z ≫ ((operation m hm hρ hρ2 hρr).component q - (GlobalThomTime.operation m hρ hρr).component q) =
      z ≫ timeCorrection m hm hρ hρ2 hρr q ≫ (chains (TopCat.of (neighborhood (m + 1) r))).d (q + 1) q := by
  have he := TimePrismCapCoboundaryAllDegrees.cycle_boundary (SelfCutTimePrism.chainHomotopy (m + 1))
    (m + q) q (primitiveCap m hm hρ hρ2 hρr q) (upperCap m hm hρ hρ2 hρr q) _
    (cap_boundary m hm hρ hρ2 hρr q)
    (cap_endpoint_zero m hm hρ hρ2 hρr q 0 (Or.inl rfl))
    (cap_endpoint_zero m hm hρ hρ2 hρr q 1 (Or.inr rfl)) z hz
  change z ≫ ((SelfCutTimePrism.prism (m + 1) (m + q) ≫ _) -
    (SelfCutTimePrism.prism (m + 1) (m + q) ≫ _)) = _
  rw [← Preadditive.comp_sub]
  simpa only [timeCorrection, SelfCutTimePrism.prism, Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp] using he

theorem homology_eq (q : ℕ) :
    (operation m hm hρ hρ2 hρr).homology q = (GlobalThomTime.operation m hρ hρr).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q (timeCorrection m hm hρ hρ2 hρr q)
  exact cycle_boundary m hm hρ hρ2 hρr q _ ((chains _).iCycles_d _ _)

theorem closed_test_values (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)
    (hK : cochainCoboundary (ZMod 2) _ q K = 0) {M : ModuleCat.{0} (ZMod 2)}
    (z : M ⟶ (chains (TopCat.of (SphereLoop (m + 1)))).X (m + q))
    (hz : z ≫ (chains (TopCat.of (SphereLoop (m + 1)))).d (m + q) (m + q - 1) = 0) :
    z ≫ (operation m hm hρ hρ2 hρr).component q ≫ K =
      z ≫ (GlobalThomTime.operation m hρ hρr).component q ≫ K := by
  have he := congrArg (fun f => f ≫ K) (cycle_boundary m hm hρ hρ2 hρr q z hz)
  change (chains (TopCat.of (neighborhood (m + 1) r))).d (q + 1) q ≫ K = 0 at hK
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hK, comp_zero] at he
  exact sub_eq_zero.mp he

end
end Finsler.ComplementThomTimeComparison
