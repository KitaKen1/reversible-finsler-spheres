module

public import Finsler.Loop.OriginalFirstHalfAnnularJoinFirstIdentity
public import Finsler.Loop.OriginalFirstHalfAnnularInputRefinement
public import Finsler.Loop.RelativeTimeCapOnSmallInput
public import Finsler.Loop.OriginalFirstHalfSequentialTimeComparison
public import Finsler.Loop.SingleCapTimeRetraction

/-! The genuine spatial-cap-before-time arrangement agrees with
the original time-before-cap sequential operation by a real relative
double prism and actual input refinement, in the identical target. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfAnnularTimeAssembly

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfCupOrderCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η : ℝ)
  {κ : ℝ} (hκ : 0 < κ) (h2κR : 2 * κ ≤ R) (hκR : κ < R)
  (hη : 0 < η) (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def commonCap := (OriginalFirstHalfSequentialJoinGamma.operation α β R r η hR hr h p T hκ F B goodΓ hT).pre
  (OriginalFirstHalfAnnularCommonCover.toSequential α β R r η κ ρ)

theorem common_source (q : ℕ) :
    (commonCap α β R r η hκ hR hr h p T F B goodΓ hT).component q ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)).f
      ((((m + 1) + (m + p)) + 1) + q) ≫
      RelativeCapAssociativity.absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
        ((((m + 1) + (m + p)) + 1) + q) rfl (originalOrder α β r hr h p T hκ false) := by
  dsimp only [commonCap, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, OriginalFirstHalfSequentialJoinGamma.component_source, ← Category.assoc]
  have hi := congrArg (fun k => k.f ((((m + 1) + (m + p)) + 1) + q))
    (OriginalFirstHalfAnnularCommonCover.toSequential_inclusion α β R r η κ ρ)
  simp only [HomologicalComplex.comp_f] at hi
  rw [hi]
  rfl

def commonTime := OriginalFirstHalfSequentialTimeComparison.fromCap α β R r hR hr h p T hκ F B
  (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
  (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)
  (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr)
  (commonCap α β R r η hκ hR hr h p T F B goodΓ hT)
  (common_source α β R r η hκ hR hr h p T F B goodΓ hT)

theorem common_normal (q : ℕ) :
    (commonTime α β R r η hκ hκR hη hR hr h hρr p T F B goodΓ hT).component q =
    AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      (smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
        (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)
        (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr)).f
        (((m + 1) + (m + p)) + q + 1) ≫
      SingleCapTimeRefinement.aligned ((m + 1) + (m + p))
        (commonCap α β R r η hκ hR hr h p T F B goodΓ hT) q := by
  change AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
    SingleCapTimePrism.aligned (TopCat.of (P × Q)) (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
      (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr)
      _ ((m + 1) + (m + p)) (commonCap α β R r η hκ hR hr h p T F B goodΓ hT) q = _
  rw [SingleCapTimePrism.aligned_normal]
  simpa only [Category.assoc] using congrArg
    (fun k => AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫ k)
    (SingleCapTimeRetraction.normal
      (smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
        (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)
        (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr))
      ((m + 1) + (m + p)) (commonCap α β R r η hκ hR hr h p T F B goodΓ hT) q)

theorem input_component (q : ℕ) :
    (inclusion (TopCat.of (P × Q)) (OriginalFirstHalfAnnularInputRefinement.cover α β R r η κ ρ)).f
      (((m + 1) + (m + p)) + q) ≫
      (OriginalFirstHalfAnnularJoinFirstIdentity.joined α β R hκ h2κR p r η hη hR hr h hρr T F B goodΓ hT).component q =
    (inclusion (TopCat.of (P × Q)) (OriginalFirstHalfAnnularInputRefinement.cover α β R r η κ ρ)).f
      (((m + 1) + (m + p)) + q) ≫
      AnnularTimeTrim.prism (TopCat.of (P × Q)) (((m + 1) + (m + p)) + q) ≫
      (smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfAnnularJoinCover.cover α β κ)
        (OriginalFirstHalfAnnularJoinCover.cover_open α β κ)
        (OriginalFirstHalfAnnularJoinCover.cover_univ α β κ hκ)).f (((m + 1) + (m + p)) + q + 1) ≫
      SingleCapTimeRefinement.aligned ((m + 1) + (m + p))
        (OriginalFirstHalfAnnularCoarseCap.coarse α β R r η hκ h2κR hη hρr hR hr h p T F B goodΓ hT) q := by
  let V := OriginalFirstHalfAnnularJoinCover.cover α β κ
  let Rt := smallSingularRetraction (X := ambient α β) coeff V
    (OriginalFirstHalfAnnularJoinCover.cover_open α β κ) (OriginalFirstHalfAnnularJoinCover.cover_univ α β κ hκ)
  have hs : inclusion (ambient α β) V ≫ Rt = 𝟙 _ := ι_comp_smallSingularRetraction (X := ambient α β) coeff V
    (OriginalFirstHalfAnnularJoinCover.cover_open α β κ) (OriginalFirstHalfAnnularJoinCover.cover_univ α β κ hκ)
  have hp (i : ℕ) : OriginalFirstHalfAnnularJoinCover.prism α β κ i =
      (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f i ≫
        AnnularTimeTrim.prism (TopCat.of (P × Q)) i ≫ Rt.f (i + 1) := by
    have ht := congrArg (fun k => k ≫ Rt.f (i + 1)) (OriginalFirstHalfAnnularJoinCover.prism_inclusion α β κ i)
    simp only [Category.assoc] at ht
    rw [← HomologicalComplex.comp_f, hs, HomologicalComplex.id_f, Category.comp_id] at ht
    exact ht.symm
  calc
    _ = (OriginalFirstHalfAnnularInputRefinement.toSpatial α β R r η κ ρ).f (((m + 1) + (m + p)) + q) ≫
        ((inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (((m + 1) + (m + p)) + q) ≫
          (OriginalFirstHalfAnnularJoinFirstIdentity.joined α β R hκ h2κR p r η hη hR hr h hρr T F B goodΓ hT).component q) := by
      rw [← Category.assoc, ← HomologicalComplex.comp_f, OriginalFirstHalfAnnularInputRefinement.toSpatial_inclusion]
    _ = _ := by
      rw [OriginalFirstHalfAnnularJoinFirstIdentity.on_small, hp]
      simp only [Rt, V, ← Category.assoc, ← HomologicalComplex.comp_f,
        OriginalFirstHalfAnnularInputRefinement.toSpatial_inclusion]

theorem joined_common (q : ℕ) :
    (OriginalFirstHalfAnnularJoinFirstIdentity.joined α β R hκ h2κR p r η hη hR hr h hρr T F B goodΓ hT).homology q =
    (commonTime α β R r η hκ hκR hη hR hr h hρr p T F B goodΓ hT).homology q := by
  apply RelativeTimeCapOnSmallInput.homology_eq (TopCat.of (P × Q)) (ambient α β)
    (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ) (OriginalFirstHalfAnnularJoinCover.cover α β κ)
    Prod.fst (fun _ _ hz => hz.1)
    (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr)
    (OriginalFirstHalfAnnularJoinCover.cover_open α β κ) (OriginalFirstHalfAnnularJoinCover.cover_univ α β κ hκ)
    (OriginalFirstHalfAnnularInputRefinement.cover α β R r η κ ρ)
    (OriginalFirstHalfAnnularInputRefinement.cover_open α β R r η κ ρ)
    (OriginalFirstHalfAnnularInputRefinement.cover_univ α β R r η κ ρ hη hκ hκR hρr)
    (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0) (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1)
    ((AnnularTimeTrim.cylinder (TopCat.of (P × Q))).toSSet.chainComplexMap coeff)
    (OriginalFirstHalfAnnularInputRefinement.zero α β R r η κ ρ) (OriginalFirstHalfAnnularInputRefinement.one α β R r η κ ρ)
    (OriginalFirstHalfAnnularInputRefinement.zero_inclusion α β R r η κ ρ).symm
    (OriginalFirstHalfAnnularInputRefinement.one_inclusion α β R r η κ ρ).symm
    _ ((m + 1) + (m + p)) (commonCap α β R r η hκ hR hr h p T F B goodΓ hT)
    (OriginalFirstHalfAnnularCoarseCap.coarse α β R r η hκ h2κR hη hρr hR hr h p T F B goodΓ hT)
    (OriginalFirstHalfAnnularCoarseCap.coarse_on_common α β R r η hκ h2κR hη hρr hR hr h p T F B goodΓ hT)
    _ _ (input_component α β R r η hκ h2κR hη hR hr h hρr p T F B goodΓ hT)
    (common_normal α β R r η hκ hκR hη hR hr h hρr p T F B goodΓ hT) q

theorem sequential_common (q : ℕ) :
    (OriginalFirstHalfSequentialTimeComparison.onJoin α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).homology q =
    (commonTime α β R r η hκ hκR hη hR hr h hρr p T F B goodΓ hT).homology q := by
  apply SingleCapTimePrismComparison.homology_eq (TopCat.of (P × Q))
    (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ)
    Prod.snd (fun _ _ hz => hz.2)
    (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr)
    (OriginalFirstHalfJoinTimeCover.cover_open α β R r η ρ κ)
    (OriginalFirstHalfJoinTimeCover.cover_univ α β R r η ρ hη hκR hρr)
    _ _ (commonCap α β R r η hκ hR hr h p T F B goodΓ hT)
    (OriginalFirstHalfSequentialJoinGamma.operation α β R r η hR hr h p T hκ F B goodΓ hT)
    (inner α β δ) (originalOrder α β r hr h p T hκ false) (original_inner_zero α β r hr h p T hκ false)
    (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
    (OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B)
    (common_source α β R r η hκ hR hr h p T F B goodΓ hT)
    (OriginalFirstHalfSequentialJoinGamma.component_source α β R r η hR hr h p T hκ F B goodΓ hT)
    (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
    (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)
    (fun _ => rfl) q

theorem joined_sequential (q : ℕ) :
    (OriginalFirstHalfAnnularJoinFirstIdentity.joined α β R hκ h2κR p r η hη hR hr h hρr T F B goodΓ hT).homology q =
    (OriginalFirstHalfSequentialTimeComparison.onJoin α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).homology q :=
  (joined_common α β R r η hκ h2κR hκR hη hR hr h hρr p T F B goodΓ hT q).trans
    (sequential_common α β R r η hκ hκR hη hR hr h hρr p T F B goodΓ hT q).symm

end
end Finsler.OriginalFirstHalfAnnularTimeAssembly
