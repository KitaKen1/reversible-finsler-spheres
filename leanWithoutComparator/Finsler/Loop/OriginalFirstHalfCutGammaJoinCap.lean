module

public import Finsler.Loop.OriginalFirstHalfCutGammaJoinCover
public import Finsler.Loop.LiftedCapCochainBoundary

/-! The genuine first gamma cap lands directly in actual retained-
output join small chains on the full proper cut x Q space. Local
coboundary removal proves closure without ambient gamma closure. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutGammaJoinCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfCutOutputJoinData
open Finsler.OriginalFirstHalfCutProductCochains Finsler.OriginalFirstHalfCutGammaJoinCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

private theorem coboundary_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (ξ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f (d + 1) (cochainCoboundary (ZMod 2) Y d ξ) =
      cochainCoboundary (ZMod 2) X d (cochainPullback f d ξ) :=
  (ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm d (d + 1)) ξ).symm

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

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem parent_image (q : ℕ)
    (σ : ((ambient α β).smallSingularSubcomplex (cover α β r hr κ ρ) : SSet) _⦋((m + 1) + p) + q⦌)
    (hσ : (TopCat.toSSet.obj (ambient α β)).ιChainComplex σ.val ≫
      absoluteChain (ambient α β) ((m + 1) + p) q (((m + 1) + p) + q) rfl
        (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T) ≠ 0) :
    ∃ i, Set.range ((ambient α β).toSSetObjEquiv _ σ.val) ⊆ originalTime α r (Q := Q) ''
      CompactJoinCapLocalization.cover (kept α r hr) β κ i := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β) (cover α β r hr κ ρ) σ.val).mp σ.property
  cases i with
  | none => exact (hσ (SupportedCap.cap_zero_on_simplex _ _ ((m + 1) + p) q (((m + 1) + p) + q) rfl _
      (gamma_cut_far_zero α β r hr h p T) σ.val hi)).elim
  | some i => exact ⟨i, hi.trans (near_image α β r hr κ ρ i)⟩

def component := SmallCapSubspaceLift.component (ambient α β) (space α r (Q := Q)) (cutDomain α β r)
  (cutIso α β r) (cover α β r hr κ ρ) (CompactJoinCapLocalization.cover (kept α r hr) β κ) ((m + 1) + p)
  (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)
  (fun q σ hσ => by rw [source_eq]; exact parent_image α β r hr κ h p T q σ hσ)

theorem component_source (q : ℕ) :
    component α β r hr κ h p T q ≫
      (inclusion (space α r (Q := Q)) (CompactJoinCapLocalization.cover (kept α r hr) β κ)).f q ≫
        (push (originalTime α r (Q := Q))).f q =
    (inclusion (ambient α β) (cover α β r hr κ ρ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α β) ((m + 1) + p) q (((m + 1) + p) + q) rfl
        (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T) := by
  have hc := SmallCapSubspaceLift.component_inclusion (ambient α β) (space α r (Q := Q)) (cutDomain α β r)
    (cutIso α β r) (cover α β r hr κ ρ) (CompactJoinCapLocalization.cover (kept α r hr) β κ) ((m + 1) + p)
    (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)
    (fun q σ hσ => by rw [source_eq]; exact parent_image α β r hr κ h p T q σ hσ) q
  simpa only [component, SmallCapSubspaceLift.target, HomologicalComplex.comp_f, source_eq, Category.assoc] using hc

theorem target_mono (q : ℕ) : Mono (((inclusion (space α r (Q := Q))
    (CompactJoinCapLocalization.cover (kept α r hr) β κ)) ≫ push (originalTime α r (Q := Q))).f q) := by
  have ht := SmallCapSubspaceLift.target_mono (ambient α β) (space α r (Q := Q)) (cutDomain α β r)
    (cutIso α β r) (CompactJoinCapLocalization.cover (kept α r hr) β κ) q
  simpa only [SmallCapSubspaceLift.target, source_eq] using ht

variable (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hT in
theorem proper_boundary_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutDomain α β r)) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + p)
        (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)) = 0 := by
  have hs : (cutIso α β r).inv ≫ originalTime α r (Q := Q) =
      SupportedCap.subspaceMap (ambient α β) (cutDomain α β r) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have hz : cochainPullback (originalTime α r (Q := Q)) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + p)
        (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)) = 0 := by
    rw [coboundary_pullback, source_gamma]
    exact gamma_closed α r hr h p T hT (Q := Q)
  have he := congrArg (cochainPullback (cutIso α β r).inv (((m + 1) + p) + 1)) hz
  rw [← pullback_comp, hs] at he
  simpa only [cochainPullback, map_zero] using he

include hT in
theorem cover_boundary_zero (i : Option (CompactRotatedCutData.source α r × Q)) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cover α β r hr κ ρ i)) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + p)
        (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)) = 0 := by
  cases i with
  | none =>
      change cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (((m + 1) + p) + 1)
        (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + p)
          (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)) = 0
      rw [coboundary_pullback, gamma_cut_far_zero]
      exact map_zero _
  | some i =>
      apply restriction_zero_subset (ambient α β) _ (cutDomain α β r)
        (fun z hz => show distance (m + 1) (z.1, α z.2.1) ≤ r from hz.2.le)
        (((m + 1) + p) + 1) _ (proper_boundary_zero α β r hr h p T hT)

include hT in
theorem small_boundary_zero (q : ℕ) :
    (inclusion (ambient α β) (cover α β r hr κ ρ)).f ((((m + 1) + p) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + p) + 1) q ((((m + 1) + p) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + p)
          (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)) = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((ambient α β).smallSingularSubcomplex (cover α β r hr κ ρ) : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β) (cover α β r hr κ ρ) σ.val).mp σ.property
  simp only [SmallChainCarrier.inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  exact SupportedCap.cap_zero_on_simplex _ _ _ q _ rfl _
    (cover_boundary_zero α β r hr κ h p T hT i) σ.val hi

include hT in
theorem component_comm (q : ℕ) :
    component α β r hr κ h p T (q + 1) ≫
      (small (space α r (Q := Q)) (CompactJoinCapLocalization.cover (kept α r hr) β κ)).d (q + 1) q =
    (small (ambient α β) (cover α β r hr κ ρ)).d (((m + 1) + p) + (q + 1)) (((m + 1) + p) + q) ≫
      component α β r hr κ h p T q := by
  have hb := LiftedCapCochainBoundary.boundary (cover α β r hr κ ρ)
    (small (space α r (Q := Q)) (CompactJoinCapLocalization.cover (kept α r hr) β κ))
    (inclusion (space α r (Q := Q)) (CompactJoinCapLocalization.cover (kept α r hr) β κ) ≫ push (originalTime α r (Q := Q)))
    (target_mono α β r hr κ) ((m + 1) + p) (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)
    (component α β r hr κ h p T) (fun _ => 0)
    (fun q => by simpa only [HomologicalComplex.comp_f, Category.assoc] using component_source α β r hr κ h p T q)
    (fun q => by rw [zero_comp, small_boundary_zero α β r hr κ h p T hT q]) q
  simpa only [comp_zero, sub_zero] using hb

def operation : DegreeLoweringHomology.Map (small (ambient α β) (cover α β r hr κ ρ))
    (small (space α r (Q := Q)) (CompactJoinCapLocalization.cover (kept α r hr) β κ)) ((m + 1) + p) where
  component := component α β r hr κ h p T
  comm := component_comm α β r hr κ h p T hT

end
end Finsler.OriginalFirstHalfCutGammaJoinCap
