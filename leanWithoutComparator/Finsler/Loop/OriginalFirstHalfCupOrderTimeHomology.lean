module

public import Finsler.Loop.OriginalFirstHalfCupOrderBounded
public import Finsler.Loop.OriginalFirstHalfCupOneTimeBoundary
public import Finsler.Loop.SingleCapTimePrism
public import Finsler.Loop.TimePrismCapCoboundaryAnySource
public import Finsler.Topology.DegreeLoweringExact

/-! The two actual closed bounded cup-order time operations agree
on ordinary-input homology, already in their identical proper target.
The real primitive prism supplies the comparison boundary. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCupOrderTimeHomology

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJointSupportedCap
open Finsler.OriginalFirstHalfCupOrderCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)
  (hκR : κ < R) (F : ReversibleMetric (m + 1)) (B η : ℝ) (hη : 0 < η) (hρr : ρ < r)
  (good : ∀ b, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (properOrder α β R r hR hr h p T hκ b))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def operation (b : Bool) : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p)) :=
  SingleCapTimePrism.operation (TopCat.of (P × Q)) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p))
    (OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η good b hT)
    (inner α β δ) (originalOrder α β r hr h p T hκ b) (original_inner_zero α β r hr h p T hκ b)
    (push (source α β R r hR hr F B)) (source_mono α β R r hR hr F B)
    (OriginalFirstHalfCupOrderBounded.cap_source α β R r hR hr h p T hκ F B η good b)
    (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
    (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)

theorem component_normal (b : Bool) (q : ℕ) :
    (operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT b).component q =
    AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (chains (ambient α β)).X
        (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      OriginalFirstHalfCupOrderBounded.cap α β R r hR hr h p T hκ F B η good b q := by
  change AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
    SingleCapTimePrism.aligned (TopCat.of (P × Q)) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
      (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p))
      (OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η good b hT) q = _
  rw [SingleCapTimePrism.aligned_normal]
  rfl

variable
  (goodχ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + (m + p))
    (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ))
  (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ)))

theorem component_difference (q : ℕ) :
    (operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT false).component q -
      (operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT true).component q =
    OriginalFirstHalfCupOneTimeBoundary.timeBoundary α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q := by
  have hd := congrArg (fun c =>
    AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (chains (ambient α β)).X
        (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)).f ((((m + 1) + (m + p)) + 1) + q) ≫ c)
    (OriginalFirstHalfCupOrderBounded.difference α β R r hR hr h p T hκ F B η good goodδ hT q)
  simp only [Preadditive.comp_sub] at hd
  rw [component_normal, component_normal]
  exact hd

include goodχ goodδ in
theorem homology_eq (q : ℕ) :
    (operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT false).homology q =
      (operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT true).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (-OriginalFirstHalfCupOneTimeBoundary.timePrimitive α β R r hR hr h p T hκ hκR F B η hη hρr goodχ q)
  rw [component_difference α β R r hR hr h p T hκ hκR F B η hη hρr good hT goodδ q]
  have hh := TimePrismCapCoboundaryAnySource.cycle_boundary
    ((AnnularTimeTrim.cylinder (TopCat.of (P × Q))).toSSet.chainComplexMap coeff)
    (((m + 1) + (m + p)) + q) q (by omega)
    (OriginalFirstHalfCupOneTimeBoundary.retracted α β R r hR hr h p T hκ hκR F B η hη hρr goodχ q)
    (OriginalFirstHalfCupOneTimeBoundary.retracted α β R r hR hr h p T hκ hκR F B η hη hρr goodχ (q + 1))
    (eqToHom (congrArg (chains (ambient α β)).X
      (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
        OriginalFirstHalfCupOneTimeBoundary.boundaryRetracted α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q)
    (OriginalFirstHalfCupOneTimeBoundary.retracted_boundary α β R r hR hr h p T hκ hκR F B η hη hρr goodχ goodδ q)
    (OriginalFirstHalfCupOneTimeBoundary.endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodχ 0 (Or.inl rfl) q)
    (OriginalFirstHalfCupOneTimeBoundary.endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodχ 1 (Or.inr rfl) q)
    ((chains (TopCat.of (P × Q))).iCycles (((m + 1) + (m + p)) + q))
    ((chains (TopCat.of (P × Q))).iCycles_d _ _)
  simpa only [OriginalFirstHalfCupOneTimeBoundary.timeBoundary,
    OriginalFirstHalfCupOneTimeBoundary.timePrimitive, AnnularTimeTrim.prism,
    Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using hh

end
end Finsler.OriginalFirstHalfCupOrderTimeHomology
