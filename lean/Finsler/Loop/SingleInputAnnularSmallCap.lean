module

public import Finsler.Loop.SupportedDoubleCapNaturality
public import Finsler.Loop.FirstInputSelfCutBoundedOperations
public import Finsler.Loop.CapCupNested
public import Finsler.Topology.AnnularDoubleCap

/-! The genuine raw family cap and the global annular cut on actual
small inputs. Use the open near space for naturality, and only then
map to the original closed proper-cut carrier. -/

@[expose] public section
namespace Finsler.SingleInputAnnularSmallCap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ σ : ℝ) {ρ : ℝ}
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))

def near : Set (ambient α) := {z | SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r}

def nearToProper : TopCat.of (near α r) ⟶ OriginalFirstHalfCutNormalizedFactors.cutSpace α r :=
  TopCat.ofHom ⟨fun z => (⟨z.val,
    (show SupportedSelfCut.distance (m + 1) (z.val.1, α z.val.2) < r from z.property).le⟩ : CompactRotatedCutData.source α r),
    continuous_subtype_val.subtype_mk _⟩

def nearEvaluation : TopCat.of (near α r) ⟶ TopCat.of (SupportedSelfCut.neighborhood (m + 1) r) :=
  restriction (AnnularSelfCut.familyMap α) (near α r) (SupportedSelfCut.neighborhood (m + 1) r) (fun _ hz => hz)

def localInput := SmallRefinementComparison.refinement (OriginalFirstHalfFactorwiseCover.first σ)
  (SupportedCap.cover (ambient α) (far α ρ) (near α r)) (fun c => (firstIndex c).isSome)
  (fun c z hz => by
    have hh := hfirst c hz
    cases he : firstIndex c with
    | none => simpa only [he, cover, Option.isSome_none, SupportedCap.cover, Bool.false_eq_true, ↓reduceIte] using hh
    | some v =>
      simp only [he, cover] at hh
      exact hh.2)

def globalSmallMap := localInput α r hr κ σ firstIndex hfirst ≫
  smallMap (AnnularSelfCut.familyMap α) (far α ρ) (near α r)
    (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (fun _ hz => hz) (fun _ hz => hz)

theorem localInput_inclusion : localInput α r hr κ σ firstIndex hfirst ≫
    inclusion (ambient α) (SupportedCap.cover (ambient α) (far α ρ) (near α r)) =
      inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ) :=
  SmallRefinementComparison.refinement_inclusion _ _ _ _

theorem globalSmallMap_inclusion : globalSmallMap α r hr κ σ firstIndex hfirst ≫
    inclusion (SelfCutThomCocycle.parameters (m + 1))
      (SupportedCap.cover _ (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)) =
      inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ) ≫ push (AnnularSelfCut.familyMap α) := by
  rw [globalSmallMap, Category.assoc, smallMap_inclusion, ← Category.assoc, localInput_inclusion]

theorem near_source : nearToProper α r ≫ source α r = SupportedCap.subspaceMap (ambient α) (near α r) := by
  ext z : 1
  rfl

theorem tested_square : nearEvaluation α r ≫ TopCat.ofHom (SupportedSelfCut.tested (m + 1) hr.le) =
    nearToProper α r ≫ FirstInputRotationOriginalFactors.originalTester α r hr := by
  ext z : 1
  rfl

theorem retained_square : nearEvaluation α r ≫ TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr.le) =
    nearToProper α r ≫ TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr) := by
  ext z : 1
  rfl

variable {δ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem tested_cochain : cochainPullback (nearEvaluation α r) p
    (NormalizedSelfCut.testedCocycle (m + 1) p hr.le T) =
      cochainPullback (SupportedCap.subspaceMap (ambient α) (near α r)) p
        (FirstInputRotationZeroTimeFactors.originalTested α r hr p T) := by
  rw [NormalizedSelfCut.testedCocycle, ← pullback_comp, tested_square, pullback_comp,
    ← near_source α r, pullback_comp, FirstInputRotationZeroTimeFactors.originalTested,
    show source α r = SupportedCap.subspaceMap (ambient α) (CompactRotatedCutData.source α r) from rfl,
    TubeCochainExtension.restriction]

def localCap (q : ℕ) :=
  (localInput α r hr κ σ firstIndex hfirst).f ((m + 1) + (p + q)) ≫
  SupportedDoubleCap.localized (ambient α) (far α ρ) (near α r) (m + 1) p
    (FirstInputRotationZeroTimeFactors.originalThom α h)
    (pullback_support (AnnularSelfCut.familyMap α) (far α ρ) (SupportedSelfCut.exterior (m + 1) ρ)
      (fun _ hz => hz) (m + 1) (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h))
    (cochainPullback (SupportedCap.subspaceMap (ambient α) (near α r)) p
      (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)) q ((m + 1) + (p + q)) rfl ≫
  (push (nearToProper α r)).f q

theorem localCap_source (q : ℕ) : localCap α r hr κ σ firstIndex hfirst h p T q ≫ (push (source α r)).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap (ambient α) (m + 1) p q
        (FirstInputRotationZeroTimeFactors.originalThom α h)
        (FirstInputRotationZeroTimeFactors.originalTested α r hr p T) := by
  dsimp only [localCap, SupportedDoubleCap.localized]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, ← push_comp, near_source]
  have hn := RelativeCapBoundary.absolute_chain_natural
    (SupportedCap.subspaceMap (ambient α) (near α r)) p q (p + q) rfl
    (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)
  change absoluteChain (TopCat.of (near α r)) p q (p + q) rfl
    (cochainPullback (SupportedCap.subspaceMap (ambient α) (near α r)) p
      (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)) ≫
      (push (SupportedCap.subspaceMap (ambient α) (near α r))).f q = _ at hn
  rw [hn]
  rw [← Category.assoc (SupportedCap.localizedCap _ _ _ _ _ _ _ _ _)]
  rw [SupportedCap.localizedCap_inclusion]
  simp only [← Category.assoc]
  rw [← HomologicalComplex.comp_f, localInput_inclusion]
  rfl

theorem global_localized (q : ℕ) :
    (globalSmallMap α r hr κ σ firstIndex hfirst).f ((m + 1) + (p + q)) ≫
      SupportedDoubleCap.localized (SelfCutThomCocycle.parameters (m + 1))
        (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r) (m + 1) p
        (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.testedCocycle (m + 1) p hr.le T) q ((m + 1) + (p + q)) rfl ≫
        (push (TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr.le))).f q =
      localCap α r hr κ σ firstIndex hfirst h p T q ≫
        (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr))).f q := by
  dsimp only [globalSmallMap]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [← Category.assoc _ (SupportedDoubleCap.localized _ _ _ _ _ _ _ _ _ _ _),
    SupportedDoubleCapNaturality.localized]
  have ht := tested_cochain α r hr p T
  dsimp only [nearEvaluation] at ht
  rw [ht]
  simp only [Category.assoc]
  have hs := retained_square α r hr
  dsimp only [nearEvaluation] at hs
  rw [← HomologicalComplex.comp_f, ← push_comp, hs, push_comp, HomologicalComplex.comp_f]
  rfl

variable (hρr : ρ < r) (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem annular_source (q : ℕ) :
    localCap α r hr κ σ firstIndex hfirst h p T q ≫
      (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr))).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((m + 1) + (p + q)) ≫
      (push (AnnularSelfCut.familyMap α)).f ((m + 1) + (p + q)) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
        (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
      AnnularCutComparison.cut m p h hρr hr.le T hT q := by
  rw [← global_localized α r hr κ σ firstIndex hfirst h p T q]
  exact (AnnularDoubleCap.canonical_cut_on_small m p h hρr hr.le T
    (OriginalFirstHalfFactorwiseCover.first σ) (AnnularSelfCut.familyMap α)
    (globalSmallMap α r hr κ σ firstIndex hfirst)
    (globalSmallMap_inclusion α r hr κ σ firstIndex hfirst) hT q).symm

end
end Finsler.SingleInputAnnularSmallCap
