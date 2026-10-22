module

public import Finsler.Loop.SupportedTestOrderThomCarrier
public import Finsler.Loop.NativeBVThomBoundary
public import Finsler.Loop.GeometricTimeCupInterval
public import Finsler.Loop.SupportedIntervalFaces

/-! Projection past the ORIGINAL supported Thom cap for a literal source
factor. The explicit subdivision/cup-one primitive retains the actual
diagonal and far carriers, hence both original time endpoints. -/
@[expose] public section
namespace Finsler.NativeSourceThomProjection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

private theorem dual_at (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (A : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q) :
    RelativeCapAssociativity.absoluteChain X p q N h A ≫ B = CupOne.cup X p q N h A B := by
  subst N
  rw [RelativeCapDual.absolute_chain_dual, CupOne.cup_comparison]

def sourceMap (m : ℕ) : parameters (m + 1) ⟶ Loops (m + 1) :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (p q : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
  (B : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)

def alpha := cochainPullback (sourceMap m) p E

def near : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) (p + q) :=
  cochainCup p q
    (cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (neighborhood (m + 1) r)) p (alpha m p E)) B

def primitive : singularCochainGroup (ZMod 2) (parameters (m + 1)) ((p + m) + q) :=
  SupportedCapTestOrder.primitive _ (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) p m q
    (alpha m p E) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported _ _ _) B

def outside : singularCochainGroup (ZMod 2) (parameters (m + 1)) ((p + m) + q + 1) :=
  CupOne.cup _ p ((m + 1) + q) ((p + m) + q + 1) (by omega)
    (alpha m p E) (NativeBVThomBoundary.parameter m hρ hρr q B)

def inside : singularCochainGroup (ZMod 2) (parameters (m + 1)) ((p + m) + q + 1) :=
  CochainDegreeTransport.pre _ (show (p + m) + q + 1 = (m + 1) + (p + q) by omega)
    (NativeBVThomBoundary.parameter m hρ hρr (p + q) (near m p q E B))

theorem before_eq : SupportedCapTestOrderCoupling.before _ (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) p m q
    (alpha m p E) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported _ _ _) B = outside m hρ hρr p q E B := by
  unfold SupportedCapTestOrderCoupling.before outside
  exact dual_at _ _ _ _ _ _ _

theorem after_eq : SupportedCapTestOrderCoupling.after _ (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) p m q
    (alpha m p E) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported _ _ _) B = inside m hρ hρr p q E B := by
  unfold SupportedCapTestOrderCoupling.after
  rw [RelativeCapDual.absolute_chain_dual]
  exact (NormalizedCutScalarPullback.pre_cut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) p E = 0)
    (hB : cochainCoboundary (ZMod 2) _ q B = 0) :
    cochainCoboundary (ZMod 2) _ ((p + m) + q) (primitive m hρ hρr p q E B) =
      outside m hρ hρr p q E B - inside m hρ hρr p q E B := by
  have h := SupportedCapTestOrder.boundary _ (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) p m q
    (alpha m p E) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported _ _ _) B
    (pullback_closed _ _ _ hE) (NormalizedSelfCut.cocycle_closed _ _ _) hB
  rw [before_eq, after_eq] at h
  exact h

theorem primitive_thom_zero (S : Set (parameters (m + 1)))
    (hS : cochainPullback (SupportedCap.subspaceMap _ S) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) = 0) :
    cochainPullback (SupportedCap.subspaceMap _ S) ((p + m) + q) (primitive m hρ hρr p q E B) = 0 :=
  SupportedTestOrderThomCarrier.primitive_zero _ _ _ _ _ _ _ _ _ _ _ _ _ S hS

theorem primitive_diagonal {X : TopCat.{0}} (f : X ⟶ parameters (m + 1))
    (hf : ∀ x, f x ∈ FilteredGlobalThomTime.endpointCarrier (m + 1)) :
    cochainPullback f ((p + m) + q) (primitive m hρ hρr p q E B) = 0 :=
  SupportedIntervalFaces.map_zero f (FilteredGlobalThomTime.endpointCarrier (m + 1)) hf _ _
    (primitive_thom_zero m hρ hρr p q E B _ (FilteredGlobalThomTime.cocycle_endpoint m hρ))

theorem primitive_far {X : TopCat.{0}} (f : X ⟶ parameters (m + 1))
    (hf : ∀ x, f x ∈ exterior (m + 1) ρ) :
    cochainPullback f ((p + m) + q) (primitive m hρ hρr p q E B) = 0 :=
  SupportedIntervalFaces.map_zero f (exterior (m + 1) ρ) hf _ _
    (primitive_thom_zero m hρ hρr p q E B _ (NormalizedSelfCut.cocycle_supported _ _ _))

theorem primitive_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (atTime (m + 1) t) ((p + m) + q) (primitive m hρ hρr p q E B) = 0 := by
  apply primitive_diagonal
  intro u
  rcases ht with rfl | rfl
  · rfl
  · exact (sphereRepresentative_endpoints u).symm

end
end Finsler.NativeSourceThomProjection
