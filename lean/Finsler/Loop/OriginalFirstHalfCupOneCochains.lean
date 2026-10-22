module

public import Finsler.Loop.FirstInputRotationZeroTimeFactors
public import Finsler.Loop.FirstInputRotationAmbientCupOneCarrier

/-! The genuine cup-one cochains on the original cut-time x P x Q
cylinder, before the spatial join cap is localized. At rotation zero
their restriction is exactly the already constructed near-pair model. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCupOneCochains

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.CompactH1Alignment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}

abbrev ambient (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) : TopCat.{0} :=
  TopCat.of (ClosedInterval × (P × Q))

variable (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))

def spatial : ambient α β ⟶ TopCat.of (P × Q) :=
  TopCat.ofHom ⟨fun z => z.2, continuous_snd⟩

def firstInput : ambient α β ⟶ TopCat.of (ClosedInterval × P) :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.1), continuous_fst.prodMk (continuous_fst.comp continuous_snd)⟩

def nearSource (R : ℝ) : TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶ ambient α β :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.val), by fun_prop⟩

def rotatingZero (R : ℝ) : TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶
    FirstInputRotationAmbientCover.ambient α β R :=
  FirstInputRotationTimeEndpoints.cylinderSlice α β R 0 ≫ FirstInputRotationCutCylinder.reorder α β R

def join {κ : ℝ} (hκ : 0 < κ) : singularCochainGroup (ZMod 2) (ambient α β) (m + 1) :=
  cochainPullback (spatial α β) (m + 1) (CompactJoinCocycle.cocycle α β (by omega) hκ)

variable (r : ℝ) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def gamma : singularCochainGroup (ZMod 2) (ambient α β) ((m + 1) + p) :=
  cochainPullback (firstInput α β) ((m + 1) + p)
    (FirstInputRotationZeroTimeFactors.originalGamma α r hr h p T)

def primitive {κ : ℝ} (hκ : 0 < κ) :
    singularCochainGroup (ZMod 2) (ambient α β) ((m + 1) + (m + p)) :=
  CupOne.cupOne (ambient α β) (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega)
    (join α β hκ) (gamma α β r hr h p T)

def error {κ : ℝ} (hκ : 0 < κ) :
    singularCochainGroup (ZMod 2) (ambient α β) (((m + 1) + (m + p)) + 1) :=
  CupOne.cupOne (ambient α β) (m + 1) (((m + 1) + p) + 1) (((m + 1) + (m + p)) + 1) (by omega)
    (join α β hκ) (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + p) (gamma α β r hr h p T))

theorem join_closed {κ : ℝ} (hκ : 0 < κ) :
    cochainCoboundary (ZMod 2) (ambient α β) (m + 1) (join α β hκ) = 0 :=
  pullback_closed (spatial α β) (m + 1) _ (CompactJoinCocycle.cocycle_closed α β (by omega) hκ)

theorem join_near (R : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (nearSource α β R) (m + 1) (join α β hκ) =
      cochainPullback (rotatingZero α β R) (m + 1) (FirstInputRotationAmbientCupOne.join α β R hκ) := by
  rw [join, FirstInputRotationAmbientCupOne.join, ← pullback_comp, ← pullback_comp]
  rfl

theorem gamma_near (R : ℝ) (hR : R ≤ 1 / 2) :
    cochainPullback (nearSource α β R) ((m + 1) + p) (gamma α β r hr h p T) =
      cochainPullback (rotatingZero α β R) ((m + 1) + p)
        (FirstInputRotationAmbientCupOne.gamma α β R r hR hr h p T) := by
  have he := FirstInputRotationZeroTimeFactors.gamma_zero α β R r hR hr h p T
  dsimp only [FirstInputRotationCutCylinder.thom, FirstInputRotationCutCylinder.tested] at he
  rw [← cochainCup_naturality, ← pullback_comp] at he
  rw [gamma, ← pullback_comp]
  exact he.symm

theorem primitive_near (R : ℝ) (hR : R ≤ 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (nearSource α β R) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ) =
      cochainPullback (rotatingZero α β R) ((m + 1) + (m + p))
        (FirstInputRotationAmbientCupOne.primitive α β R r hR hr h p T hκ) := by
  rw [primitive, CupOne.naturality, join_near, gamma_near α β r hr h p T R hR]
  exact (CupOne.naturality (rotatingZero α β R) (m + 1) ((m + 1) + p)
    ((m + 1) + (m + p)) (by omega) _ _).symm

theorem boundary_with_error {κ : ℝ} (hκ : 0 < κ) :
    cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ) +
      error α β r hr h p T hκ =
    CupOne.cup (ambient α β) (m + 1) ((m + 1) + p) (((m + 1) + (m + p)) + 1) (by omega)
      (join α β hκ) (gamma α β r hr h p T) -
    CupOne.cup (ambient α β) ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) (by omega)
      (gamma α β r hr h p T) (join α β hκ) := by
  have he := CupOne.boundary_formula (ambient α β) (m + 1) ((m + 1) + p)
    ((m + 1) + (m + p)) (by omega) (join α β hκ) (gamma α β r hr h p T)
  rw [join_closed, CupOne.zero_left, add_zero] at he
  exact he

def joinFar (κ : ℝ) : Set (ambient α β) :=
  spatial α β ⁻¹' NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q)
    (fun x => basepoint (α x)) (fun y => basepoint (β y)) κ

def cutFar (ρ : ℝ) : Set (ambient α β) :=
  {z | ρ < distance (m + 1) (z.1, α z.2.1)}

def inner (δ : ℝ) : Set (ambient α β) :=
  {z | distance (m + 1) (z.1, α z.2.1) ≤ δ}

theorem join_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) (m + 1)
      (join α β hκ) = 0 :=
  pullback_support (spatial α β) (joinFar α β κ) _ (fun _ hz => hz) (m + 1) _
    (CompactJoinCocycle.cocycle_far_zero α β (by omega) hκ)

theorem gamma_cut_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) ((m + 1) + p)
      (gamma α β r hr h p T) = 0 := by
  rw [gamma, FirstInputRotationZeroTimeFactors.originalGamma, cochainCup_naturality, cochainCup_naturality]
  have ht : cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (m + 1)
      (cochainPullback (firstInput α β) (m + 1) (FirstInputRotationZeroTimeFactors.originalThom α h)) = 0 := by
    rw [FirstInputRotationZeroTimeFactors.originalThom, AnnularSelfCut.familyCocycle,
      ← pullback_comp (firstInput α β) (AnnularSelfCut.familyMap α)]
    apply pullback_support (firstInput α β ≫ AnnularSelfCut.familyMap α) (cutFar α β ρ)
      (exterior (m + 1) ρ) _ (m + 1) (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
    intro z hz
    exact hz
  rw [ht, cochainCup_zero_left]

theorem primitive_join_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) = 0 :=
  CupOne.restriction_zero _ (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega) _ _
    (Or.inl (join_far_zero α β hκ))

theorem primitive_cut_far_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) = 0 :=
  CupOne.restriction_zero _ (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega) _ _
    (Or.inr (gamma_cut_far_zero α β r hr h p T))

theorem primitive_inner_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) ((m + 1) + (m + p))
      (primitive α β r hr h p T hκ) = 0 := by
  apply CupOne.restriction_zero _ (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega) _ _ (Or.inr ?_)
  rw [gamma, FirstInputRotationZeroTimeFactors.originalGamma, cochainCup_naturality, cochainCup_naturality]
  have ht : cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) (m + 1)
      (cochainPullback (firstInput α β) (m + 1) (FirstInputRotationZeroTimeFactors.originalThom α h)) = 0 := by
    rw [FirstInputRotationZeroTimeFactors.originalThom, AnnularSelfCut.familyCocycle,
      ← pullback_comp (firstInput α β) (AnnularSelfCut.familyMap α)]
    apply pullback_support (firstInput α β ≫ AnnularSelfCut.familyMap α) (inner α β δ)
      {z | distance (m + 1) z ≤ δ} _ (m + 1) (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSelfCut.cocycle_small_zero (m + 1) (by omega) h)
    intro z hz
    exact hz
  rw [ht, cochainCup_zero_left]

end
end Finsler.OriginalFirstHalfCupOneCochains
