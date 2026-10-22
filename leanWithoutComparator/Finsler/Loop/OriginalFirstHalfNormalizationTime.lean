module

public import Finsler.Loop.OriginalFirstHalfNormalizationBounded
public import Finsler.Loop.OriginalFirstHalfNormalizationLocalError
public import Finsler.Loop.OriginalFirstHalfCupOrderTimeHomology
public import Finsler.Loop.TimePrismCapCoboundaryAnySource
public import Finsler.Topology.DegreeLoweringExact
public import Finsler.Loop.SingleCapSourceCollar
public import Finsler.Loop.CapCochainBoundaryPre
public import Finsler.Loop.TimePrismCapCoboundary

/-! Integrate the actual normalization primitive over the full original
time prism. Its bounded boundary compares the new normalized cup
operator with the existing original cut-first cup-time operator. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizationTime

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedSelfCut Finsler.OriginalFirstHalfCupOneCochains
open Finsler.OriginalFirstHalfJointSupportedCap Finsler.OriginalFirstHalfNormalizationBounded

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {κ : ℝ} (hκ : 0 < κ) (hκR : κ < R) (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (hη : 0 < η) (hρr : ρ < r)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + (m + p))
    (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR))
  (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR)))

def retracted (q : ℕ) : (chains (ambient α β)).X (((m + 1) + (m + p)) + q) ⟶
    (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)).f (((m + 1) + (m + p)) + q) ≫
      primitiveCap α β R r hR hr h p T hκ F B η good q

def boundaryRetracted (q : ℕ) : (chains (ambient α β)).X ((((m + 1) + (m + p)) + 1) + q) ⟶
    (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      boundaryCap α β R r hR hr h p T hκ F B η goodδ q

theorem retracted_boundary (q : ℕ) :
    retracted α β R r hR hr h p T hκ hκR F B η hη hρr good (q + 1) ≫
      (chains (TopCat.of (bounded α β R r hR hr F B))).d (q + 1) q =
    (chains (ambient α β)).d (((m + 1) + (m + p)) + (q + 1)) (((m + 1) + (m + p)) + q) ≫
      retracted α β R r hR hr h p T hκ hκR F B η hη hρr good q -
    eqToHom (congrArg (chains (ambient α β)).X
      (show ((m + 1) + (m + p)) + (q + 1) = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
        boundaryRetracted α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q :=
  CapCochainBoundaryPre.pre
    (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr))
    ((m + 1) + (m + p)) (primitiveCap α β R r hR hr h p T hκ F B η good)
    (boundaryCap α β R r hR hr h p T hκ F B η goodδ)
    (boundary α β R r hR hr h p T hκ F B η good goodδ) q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of (P × Q)) t)).f (((m + 1) + (m + p)) + q) ≫
      retracted α β R r hR hr h p T hκ hκR F B η hη hρr good q = 0 := by
  apply SingleCapSourceCollar.lift_zero (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (inner α β δ) ((m + 1) + (m + p)) (OriginalFirstHalfNormalizationCup.primitive α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.primitive_inner_zero α β r hr h p T hκ) (AnnularTimeTrim.slice (TopCat.of (P × Q)) t) _
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (chains (TopCat.of (bounded α β R r hR hr F B))) (push (source α β R r hR hr F B))
    (source_mono α β R r hR hr F B) (primitiveCap α β R r hR hr h p T hκ F B η good)
    (primitiveCap_source α β R r hR hr h p T hκ F B η good) q
  intro x
  rcases ht with rfl | rfl
  · change distance (m + 1) (0, α x.1) ≤ δ
    exact (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le
  · change distance (m + 1) (1, α x.1) ≤ δ
    exact (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le

def timePrimitive (q : ℕ) : (chains (TopCat.of (P × Q))).X (((m + 1) + (m + p)) + q) ⟶
    (chains (TopCat.of (bounded α β R r hR hr F B))).X (q + 1) :=
  AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
    retracted α β R r hR hr h p T hκ hκR F B η hη hρr good (q + 1)

def timeBoundary (q : ℕ) : (chains (TopCat.of (P × Q))).X (((m + 1) + (m + p)) + q) ⟶
    (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
    eqToHom (congrArg (chains (ambient α β)).X
      (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      boundaryRetracted α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q

theorem cycle_boundary (q : ℕ)
    (z : coeff ⟶ (chains (TopCat.of (P × Q))).X (((m + 1) + (m + p)) + q))
    (hz : z ≫ (chains (TopCat.of (P × Q))).d (((m + 1) + (m + p)) + q)
      ((((m + 1) + (m + p)) + q) - 1) = 0) :
    z ≫ timeBoundary α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q =
    -(z ≫ timePrimitive α β R r hR hr h p T hκ hκR F B η hη hρr good q) ≫
      (chains (TopCat.of (bounded α β R r hR hr F B))).d (q + 1) q :=
  TimePrismCapCoboundary.cycle_boundary ((AnnularTimeTrim.cylinder (TopCat.of (P × Q))).toSSet.chainComplexMap coeff)
    (((m + 1) + (m + p)) + q) q (by omega)
    (retracted α β R r hR hr h p T hκ hκR F B η hη hρr good q)
    (retracted α β R r hR hr h p T hκ hκR F B η hη hρr good (q + 1))
    (eqToHom (congrArg (chains (ambient α β)).X
      (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
        boundaryRetracted α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q)
    (retracted_boundary α β R r hR hr h p T hκ hκR F B η hη hρr good goodδ q)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr good 0 (Or.inl rfl) q)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr good 1 (Or.inr rfl) q) z hz

theorem retained_cycle_boundary (q : ℕ)
    (z : coeff ⟶ (chains (TopCat.of (P × Q))).X (((m + 1) + (m + p)) + q))
    (hz : z ≫ (chains (TopCat.of (P × Q))).d (((m + 1) + (m + p)) + q)
      ((((m + 1) + (m + p)) + q) - 1) = 0) :
    z ≫ timeBoundary α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q ≫
      (push (retained α β R r hR hr F B)).f q =
    -(z ≫ timePrimitive α β R r hR hr h p T hκ hκR F B η hη hρr good q ≫
      (push (retained α β R r hR hr F B)).f (q + 1)) ≫
        (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q := by
  have hb := congrArg (fun u => u ≫ (push (retained α β R r hR hr F B)).f q)
    (cycle_boundary α β R r hR hr h p T hκ hκR F B η hη hρr good goodδ q z hz)
  simp only [Preadditive.neg_comp, Category.assoc] at hb ⊢
  rw [← (push (retained α β R r hR hr F B)).comm] at hb
  exact hb


variable
  (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
  (goodOld : ∀ v, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfCupOrderCochains.properOrder α β R r hR hr h p T hκ v))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def normalizedTime : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p)) :=
  SingleCapTimePrism.operation (TopCat.of (P × Q)) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p))
    (OriginalFirstHalfNormalizationBounded.normalizedOperation α β R r hR hr h p T hκ F B η goodN hT)
    (inner α β δ) (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.order_inner_zero α β r hr h p T hκ)
    (push (source α β R r hR hr F B)) (source_mono α β R r hR hr F B)
    (OriginalFirstHalfNormalizationBounded.normalizedCap_source α β R r hR hr h p T hκ F B η goodN)
    (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
    (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)

theorem normalized_component_normal (q : ℕ) :
    (normalizedTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).component q =
    AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (chains (ambient α β)).X
        (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      OriginalFirstHalfNormalizationBounded.normalizedCap α β R r hR hr h p T hκ F B η goodN q := by
  change AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
    SingleCapTimePrism.aligned (TopCat.of (P × Q)) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
      (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p))
      (OriginalFirstHalfNormalizationBounded.normalizedOperation α β R r hR hr h p T hκ F B η goodN hT) q = _
  rw [SingleCapTimePrism.aligned_normal]
  rfl

theorem component_difference (q : ℕ) :
    (normalizedTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).component q -
      (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr goodOld hT true).component q =
    timeBoundary α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q := by
  have hd := congrArg (fun c =>
    AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (chains (ambient α β)).X
        (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
        (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)).f ((((m + 1) + (m + p)) + 1) + q) ≫ c)
    (OriginalFirstHalfNormalizationBounded.difference α β R r hR hr h p T hκ F B η goodδ goodN hT goodOld q)
  simp only [Preadditive.comp_sub] at hd
  rw [normalized_component_normal, OriginalFirstHalfCupOrderTimeHomology.component_normal]
  exact hd

include good goodδ in
theorem homology_eq (q : ℕ) :
    (normalizedTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).homology q =
      (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr goodOld hT true).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (-timePrimitive α β R r hR hr h p T hκ hκR F B η hη hρr good q)
  rw [component_difference α β R r hR hr h p T hκ hκR F B η hη hρr goodδ goodN goodOld hT q]
  have hh := TimePrismCapCoboundaryAnySource.cycle_boundary
    ((AnnularTimeTrim.cylinder (TopCat.of (P × Q))).toSSet.chainComplexMap coeff)
    (((m + 1) + (m + p)) + q) q (by omega)
    (retracted α β R r hR hr h p T hκ hκR F B η hη hρr good q)
    (retracted α β R r hR hr h p T hκ hκR F B η hη hρr good (q + 1))
    (eqToHom (congrArg (chains (ambient α β)).X
      (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
        boundaryRetracted α β R r hR hr h p T hκ hκR F B η hη hρr goodδ q)
    (retracted_boundary α β R r hR hr h p T hκ hκR F B η hη hρr good goodδ q)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr good 0 (Or.inl rfl) q)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr good 1 (Or.inr rfl) q)
    ((chains (TopCat.of (P × Q))).iCycles (((m + 1) + (m + p)) + q))
    ((chains (TopCat.of (P × Q))).iCycles_d _ _)
  simpa only [timeBoundary, timePrimitive, AnnularTimeTrim.prism,
    Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using hh

include good goodδ in
theorem retained_homology_eq (q : ℕ) :
    ((normalizedTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).post
      (push (retained α β R r hR hr F B))).homology q =
    ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr goodOld hT true).post
      (push (retained α β R r hR hr F B))).homology q := by
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    homology_eq α β R r hR hr h p T hκ hκR F B η hη hρr good goodδ goodN goodOld hT q]

end
end Finsler.OriginalFirstHalfNormalizationTime
