module

public import Finsler.Loop.OriginalFirstHalfCutThenJoinAgreement
public import Finsler.Loop.OriginalFirstHalfCupOrderTimeHomology
public import Finsler.Loop.SingleCapTimePrismComparison

/-! Actual full-time original cut-then-retained-output-join model.
Its filtered component has the literal gamma-first and normalized
join-second source formula, and relative refinement compares it to
the actual cut-first cup time model in the identical length target. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutThenJoinTime

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfCupOrderCochains
open Finsler.OriginalFirstHalfCutThenJoinCommonCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1900000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {κ : ℝ} (hκ : 0 < κ) (hκR : κ < R)
  (hη : 0 < η) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (good : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η
    (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def boundedTime := SingleCapTimePrism.operation (TopCat.of (P × Q)) (cover α β R r η κ ρ hr)
  (cover_open α β R r η κ ρ hr) (cover_univ α β R r η κ ρ hr hη hκ hκR hρr)
  (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) ((m + 1) + (m + p))
  (OriginalFirstHalfCutThenJoinAgreement.bounded α β R r η hR hr hκ h p T F B good hT)
  (inner α β δ) (originalOrder α β r hr h p T hκ true) (original_inner_zero α β r hr h p T hκ true)
  (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
  (OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B)
  (OriginalFirstHalfCutThenJoinAgreement.bounded_source α β R r η hR hr hκ h p T F B good hT)
  (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
  (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)

def operation := (boundedTime α β R r η hR hr hκ hκR hη h hρr p T F B good hT).post
  (push (OriginalFirstHalfCutOutputJoinBounded.retained α β R r hR hr F B))

theorem bounded_component_normal (q : ℕ) :
    (boundedTime α β R r η hR hr hκ hκR hη h hρr p T F B good hT).component q =
    AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (chains (ambient α β)).X
        (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      (smallSingularRetraction (X := ambient α β) coeff (cover α β R r η κ ρ hr)
        (cover_open α β R r η κ ρ hr) (cover_univ α β R r η κ ρ hr hη hκ hκR hρr)).f
        ((((m + 1) + (m + p)) + 1) + q) ≫
      (OriginalFirstHalfCutThenJoinAgreement.bounded α β R r η hR hr hκ h p T F B good hT).component q := by
  change AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
    SingleCapTimePrism.aligned (TopCat.of (P × Q)) (cover α β R r η κ ρ hr)
      (cover_open α β R r η κ ρ hr) (cover_univ α β R r η κ ρ hr hη hκ hκR hρr)
      _ ((m + 1) + (m + p))
      (OriginalFirstHalfCutThenJoinAgreement.bounded α β R r η hR hr hκ h p T F B good hT) q = _
  rw [SingleCapTimePrism.aligned_normal]

theorem geometric_component (h2κR : 2 * κ ≤ R) (q : ℕ) :
    (operation α β R r η hR hr hκ hκR hη h hρr p T F B good hT).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
    AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (chains (ambient α β)).X
        (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      (smallSingularRetraction (X := ambient α β) coeff (cover α β R r η κ ρ hr)
        (cover_open α β R r η κ ρ hr) (cover_univ α β R r η κ ρ hr hη hκ hκR hρr)).f
        ((((m + 1) + (m + p)) + 1) + q) ≫
      (OriginalFirstHalfCutThenJoinAgreement.geometric α β R r η hr hκ h2κR h p T hT).component q ≫
      (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR))).f q := by
  dsimp only [operation, DegreeLoweringHomology.Map.post]
  rw [bounded_component_normal]
  simpa only [OriginalFirstHalfCutThenJoinAgreement.filtered, DegreeLoweringHomology.Map.post, Category.assoc] using
    congrArg (fun k => AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (chains (ambient α β)).X
        (show (((m + 1) + (m + p)) + q) + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
      (smallSingularRetraction (X := ambient α β) coeff (cover α β R r η κ ρ hr)
        (cover_open α β R r η κ ρ hr) (cover_univ α β R r η κ ρ hr hη hκ hκR hρr)).f
        ((((m + 1) + (m + p)) + 1) + q) ≫ k)
      (OriginalFirstHalfCutThenJoinAgreement.filtered_component_source α β R r η hR hr hκ h2κR h p T F B good hT q)

theorem cup_common (q : ℕ) :
    (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT true).homology q =
    (boundedTime α β R r η hR hr hκ hκR hη h hρr p T F B good hT).homology q := by
  apply SingleCapTimePrismComparison.homology_eq (TopCat.of (P × Q))
    (cover α β R r η κ ρ hr) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    Prod.snd (fun _ _ hz => hz.2)
    (cover_open α β R r η κ ρ hr) (cover_univ α β R r η κ ρ hr hη hκ hκR hρr)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    _ _ (OriginalFirstHalfCutThenJoinAgreement.bounded α β R r η hR hr hκ h p T F B good hT)
    (OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η good true hT)
    (inner α β δ) (originalOrder α β r hr h p T hκ true) (original_inner_zero α β r hr h p T hκ true)
    (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
    (OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B)
    (OriginalFirstHalfCutThenJoinAgreement.bounded_source α β R r η hR hr hκ h p T F B good hT)
    (OriginalFirstHalfCupOrderBounded.cap_source α β R r hR hr h p T hκ F B η good true)
    (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
    (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)
    (fun _ => rfl) q

theorem homology_eq (q : ℕ) :
    (operation α β R r η hR hr hκ hκR hη h hρr p T F B good hT).homology q =
    ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT true).post
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B))).homology q := by
  simp only [operation, DegreeLoweringHomology.Map.post_homology, OriginalFirstHalfCutOutputJoinBounded.retained_eq]
  rw [← cup_common α β R r η hR hr hκ hκR hη h hρr p T F B good hT q]

end
end Finsler.OriginalFirstHalfCutThenJoinTime
