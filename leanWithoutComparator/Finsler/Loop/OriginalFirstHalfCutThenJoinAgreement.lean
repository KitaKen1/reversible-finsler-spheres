module

public import Finsler.Loop.OriginalFirstHalfCutThenJoinCommonCover
public import Finsler.Loop.OriginalFirstHalfCutOutputJoinBounded
public import Finsler.Loop.OriginalFirstHalfCupOrderBounded

/-! The actual gamma-first then retained-output join cap agrees
with the real bounded cut-first cup cap on a common cover. Its actual
joined-loop image factors through the identical length sublevel. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutThenJoinAgreement

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfCutOutputJoinData
open Finsler.OriginalFirstHalfCupOrderCochains Finsler.OriginalFirstHalfCutThenJoinCommonCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {κ : ℝ} (hκ : 0 < κ) (h2κR : 2 * κ ≤ R)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (good : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η
    (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def geometric := (OriginalFirstHalfCutThenJoinCap.operation α β R r hr hκ h2κR h p T hT).pre
  (toCut α β R r η κ ρ hr)

def bounded := (OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η good true hT).pre
  (toCup α β R r η κ ρ hr)

theorem geometric_source (q : ℕ) :
    (geometric α β R r η hr hκ h2κR h p T hT).component q ≫
      (push (OriginalFirstHalfCutThenJoinCap.source α β R r hr)).f q =
    (inclusion (ambient α β) (cover α β R r η κ ρ hr)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
        ((((m + 1) + (m + p)) + 1) + q) rfl (originalOrder α β r hr h p T hκ true) := by
  dsimp only [geometric, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, OriginalFirstHalfCutThenJoinCap.component_source, ← Category.assoc]
  have hi := congrArg (fun k => k.f ((((m + 1) + (m + p)) + 1) + q)) (toCut_inclusion α β R r η κ ρ hr)
  simp only [HomologicalComplex.comp_f] at hi
  rw [hi]

theorem bounded_source (q : ℕ) :
    (bounded α β R r η hR hr hκ h p T F B good hT).component q ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (cover α β R r η κ ρ hr)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
        ((((m + 1) + (m + p)) + 1) + q) rfl (originalOrder α β r hr h p T hκ true) := by
  dsimp only [bounded, DegreeLoweringHomology.Map.pre, OriginalFirstHalfCupOrderBounded.operation]
  rw [Category.assoc, OriginalFirstHalfCupOrderBounded.cap_source, ← Category.assoc]
  have hi := congrArg (fun k => k.f ((((m + 1) + (m + p)) + 1) + q)) (toCup_inclusion α β R r η κ ρ hr)
  simp only [HomologicalComplex.comp_f] at hi
  rw [hi]

theorem component_eq (q : ℕ) :
    (geometric α β R r η hr hκ h2κR h p T hT).component q =
    (bounded α β R r η hR hr hκ h p T F B good hT).component q ≫
      (push (OriginalFirstHalfCutOutputJoinBounded.toNear α β R r hR hr F B)).f q := by
  haveI := OriginalFirstHalfCutThenJoinCap.source_mono α β R r hr q
  apply (cancel_mono ((push (OriginalFirstHalfCutThenJoinCap.source α β R r hr)).f q)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← push_comp,
    OriginalFirstHalfCutOutputJoinBounded.source_square, geometric_source, bounded_source]

def filtered := (bounded α β R r η hR hr hκ h p T F B good hT).post
  (push (OriginalFirstHalfCutOutputJoinBounded.retained α β R r hR hr F B))

include h2κR in
theorem filtered_component_source (q : ℕ) :
    (filtered α β R r η hR hr hκ h p T F B good hT).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
    (geometric α β R r η hr hκ h2κR h p T hT).component q ≫
      (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR))).f q := by
  have hs := congrArg (fun k => (push k).f q)
    (OriginalFirstHalfCutOutputJoinBounded.retained_source α β R r hR hr F B)
  simp only [push_comp, HomologicalComplex.comp_f] at hs
  dsimp only [filtered, DegreeLoweringHomology.Map.post]
  rw [Category.assoc, hs, ← Category.assoc, ← component_eq α β R r η hR hr hκ h2κR h p T F B good hT q]

end
end Finsler.OriginalFirstHalfCutThenJoinAgreement
