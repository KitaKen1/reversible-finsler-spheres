module

public import Finsler.Loop.FirstInputRotationAmbientCap
public import Finsler.Loop.FirstInputRotationCupOne
public import Finsler.Topology.AdequateTubeCochain

/-! The actual ambient join/cut-tested cup-one uses the literal tested
zero extension. Its full boundary keeps that extension's coboundary;
the resulting error cap vanishes on the genuine ambient near/far cover.
The proper restriction is exactly the bounded primitive already built. -/

@[expose] public section
namespace Finsler.FirstInputRotationAmbientCupOne

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputRotationAmbientCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1)

def spatial : ambient α β R ⟶ TopCat.of (P × Q) :=
  TopCat.ofHom ⟨fun z => z.2.2.val, by fun_prop⟩

def join {κ : ℝ} (hκ : 0 < κ) : singularCochainGroup (ZMod 2) (ambient α β R) (m + 1) :=
  cochainPullback (spatial α β R) (m + 1) (CompactJoinCocycle.cocycle α β (by omega) hκ)

variable {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def gamma : singularCochainGroup (ZMod 2) (ambient α β R) ((m + 1) + p) :=
  cochainCup (m + 1) p (ambientThom α β R hR (by omega) h)
    (FirstInputRotationAmbientCap.ambientTested α β R r hR hr p T)

def primitive {κ : ℝ} (hκ : 0 < κ) :
    singularCochainGroup (ZMod 2) (ambient α β R) ((m + 1) + (m + p)) :=
  CupOne.cupOne (ambient α β R) (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega)
    (join α β R hκ) (gamma α β R r hR hr h p T)

def error {κ : ℝ} (hκ : 0 < κ) :
    singularCochainGroup (ZMod 2) (ambient α β R) (((m + 1) + (m + p)) + 1) :=
  CupOne.cupOne (ambient α β R) (m + 1) (((m + 1) + p) + 1) (((m + 1) + (m + p)) + 1) (by omega)
    (join α β R hκ) (cochainCoboundary (ZMod 2) (ambient α β R) ((m + 1) + p) (gamma α β R r hR hr h p T))

theorem source_join {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (source α β R r) (m + 1) (join α β R hκ) =
      FirstInputRotationCupOne.join α β R r hκ := by
  rw [join, ← pullback_comp]
  rfl

theorem source_gamma :
    cochainPullback (source α β R r) ((m + 1) + p) (gamma α β R r hR hr h p T) =
      FirstInputRotationCupOne.gamma α β R r hR hr h p T := by
  rw [gamma, cochainCup_naturality, thom_source α β R r hR hr,
    FirstInputRotationAmbientCap.tested_restriction]
  rfl

theorem source_primitive {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (source α β R r) ((m + 1) + (m + p)) (primitive α β R r hR hr h p T hκ) =
      FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ := by
  rw [primitive, CupOne.naturality, source_join, source_gamma]
  rfl

theorem boundary_with_error {κ : ℝ} (hκ : 0 < κ) :
    cochainCoboundary (ZMod 2) (ambient α β R) ((m + 1) + (m + p))
      (primitive α β R r hR hr h p T hκ) + error α β R r hR hr h p T hκ =
      CupOne.cup (ambient α β R) (m + 1) ((m + 1) + p) (((m + 1) + (m + p)) + 1) (by omega)
        (join α β R hκ) (gamma α β R r hR hr h p T) -
      CupOne.cup (ambient α β R) ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) (by omega)
        (gamma α β R r hR hr h p T) (join α β R hκ) := by
  have hj : cochainCoboundary (ZMod 2) (ambient α β R) (m + 1) (join α β R hκ) = 0 :=
    pullback_closed (spatial α β R) (m + 1) _ (CompactJoinCocycle.cocycle_closed α β (by omega) hκ)
  have he := CupOne.boundary_formula (ambient α β R) (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega)
    (join α β R hκ) (gamma α β R r hR hr h p T)
  rw [hj, CupOne.zero_left, add_zero] at he
  exact he

variable (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hT in
theorem gamma_boundary_parts_zero : ∀ b : Bool,
    cochainPullback (SupportedCap.subspaceMap (ambient α β R)
      (SupportedCap.cover (ambient α β R) (far α β R ρ) (proper α β R r) b)) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β R) ((m + 1) + p) (gamma α β R r hR hr h p T)) = 0 := by
  exact AdequateTubeCochain.boundary_parts_zero (ambient α β R) (far α β R ρ) (proper α β R r)
    (m + 1) p (ambientThom α β R hR (by omega) h) (ambientThom_closed α β R hR (by omega) h)
    (thom_far_zero α β R hR (by omega) h)
    (cochainPullback (properIso α β R r).inv p (FirstInputRotationCochains.tested α β R r hR hr p T))
    (pullback_closed (properIso α β R r).inv p _ (FirstInputRotationCochains.tested_closed α β R r hR hr p T hT))

include hT in
theorem error_parts_zero {κ : ℝ} (hκ : 0 < κ) : ∀ b : Bool,
    cochainPullback (SupportedCap.subspaceMap (ambient α β R)
      (SupportedCap.cover (ambient α β R) (far α β R ρ) (proper α β R r) b)) (((m + 1) + (m + p)) + 1)
      (error α β R r hR hr h p T hκ) = 0 := by
  intro b
  exact CupOne.restriction_zero _ (m + 1) (((m + 1) + p) + 1) (((m + 1) + (m + p)) + 1) (by omega) _ _
    (Or.inr (gamma_boundary_parts_zero α β R r hR hr h p T hT b))

private theorem restriction_zero_subset (X : TopCat.{0}) (U V : Set X) (hUV : U ⊆ V)
    (d : ℕ) (ξ : singularCochainGroup (ZMod 2) X d)
    (hV : cochainPullback (SupportedCap.subspaceMap X V) d ξ = 0) :
    cochainPullback (SupportedCap.subspaceMap X U) d ξ = 0 := by
  let f := restriction (𝟙 X) U V hUV
  have he : f ≫ SupportedCap.subspaceMap X V = SupportedCap.subspaceMap X U := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have hz := congrArg (cochainPullback f d) hV
  rw [← pullback_comp, he] at hz
  simpa only [cochainPullback, map_zero] using hz

include hT in
theorem error_cover_zero {κ : ℝ} (hκ : 0 < κ) (η : ℝ) (i : Option (FirstInputRotationCochains.space α β R r)) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β R) (cover α β R r η ρ i)) (((m + 1) + (m + p)) + 1)
      (error α β R r hR hr h p T hκ) = 0 := by
  cases i with
  | none => exact error_parts_zero α β R r hR hr h p T hT hκ false
  | some i =>
    apply restriction_zero_subset (ambient α β R) (cover α β R r η ρ (some i)) (proper α β R r)
      (fun z hz => show gap α β R z ≤ r from hz.2.le) _ _
    exact error_parts_zero α β R r hR hr h p T hT hκ true

include hT in
theorem error_small_cap_zero {κ : ℝ} (hκ : 0 < κ) (η : ℝ) (q : ℕ) :
    (inclusion (ambient α β R) (cover α β R r η ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β R) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (error α β R r hR hr h p T hκ) = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((ambient α β R).smallSingularSubcomplex (cover α β R r η ρ) : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β R) (cover α β R r η ρ) σ.val).mp σ.property
  simp only [SmallChainCarrier.inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  exact SupportedCap.cap_zero_on_simplex (ambient α β R) (cover α β R r η ρ i)
    (((m + 1) + (m + p)) + 1) q _ rfl _ (error_cover_zero α β R r hR hr h p T hT hκ η i) σ.val hi

end
end Finsler.FirstInputRotationAmbientCupOne
