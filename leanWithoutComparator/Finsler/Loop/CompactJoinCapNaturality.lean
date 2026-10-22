module

public import Finsler.Loop.CompactJoinCapLocalization

/-! Genuine family-pullback naturality of the actual normalized join cap,
first as a strict localized chain identity and then through the real
small-chain retractions on homology, in the actual closed near tube. -/

@[expose] public section
namespace Finsler.CompactJoinCapNaturality

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {P Q P' Q' : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [PseudoMetricSpace P'] [PseudoMetricSpace Q'] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (f : C(P', P)) (g : C(Q', Q))

def input : TopCat.of (P' × Q') ⟶ TopCat.of (P × Q) := TopCat.ofHom f ⊗ₘ TopCat.ofHom g

def nearMap (R : ℝ) := restriction (input f g)
  (CompactNearJoinParameters.tube (α.comp f) (β.comp g) R) (CompactNearJoinParameters.tube α β R) (fun _ hz => hz)

theorem nearMap_source (R : ℝ) : nearMap α β f g R ≫
    SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R) =
    SupportedCap.subspaceMap (TopCat.of (P' × Q')) (CompactNearJoinParameters.tube (α.comp f) (β.comp g) R) ≫ input f g :=
  restriction_inclusion _ _ _ _

theorem cover_maps (ρ : ℝ) (i : P' × Q') : Set.MapsTo (input f g)
    (CompactJoinCapLocalization.cover (α.comp f) (β.comp g) ρ i)
    (CompactJoinCapLocalization.cover α β ρ (f i.1, g i.2)) := fun _ hz => hz

def smallMap (ρ : ℝ) := SmallRetractionComparison.map
  (CompactJoinCapLocalization.cover (α.comp f) (β.comp g) ρ) (CompactJoinCapLocalization.cover α β ρ)
  (input f g) (fun i => (f i.1, g i.2)) (cover_maps α β f g ρ)

theorem smallMap_source (ρ : ℝ) : smallMap α β f g ρ ≫
    inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β ρ) =
    inclusion (TopCat.of (P' × Q')) (CompactJoinCapLocalization.cover (α.comp f) (β.comp g) ρ) ≫ push (input f g) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

theorem cocycle_pullback (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (input f g) n (CompactJoinCocycle.cocycle α β hn hρ) =
      CompactJoinCocycle.cocycle (α.comp f) (β.comp g) hn hρ := by
  rw [CompactJoinCocycle.cocycle, ← pullback_comp]
  rfl

variable (hn : 1 ≤ n) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R)

theorem component (k : ℕ) : (smallMap α β f g ρ).f (n + k) ≫
    (CompactJoinCapLocalization.localized α β hn hρ hρR).component k =
    (CompactJoinCapLocalization.localized (α.comp f) (β.comp g) hn hρ hρR).component k ≫
      (push (nearMap α β f g R)).f k := by
  have : Mono ((push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f k) :=
    SupportedCap.subspacePush_mono _ _ _
  apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f k)).mp
  have hj := congrArg (fun z => (push z).f k) (nearMap_source α β f g R)
  simp only [push_comp, HomologicalComplex.comp_f] at hj
  have hncap := RelativeCapBoundary.absolute_chain_natural (input f g) n k (n + k) rfl
    (CompactJoinCocycle.cocycle α β hn hρ)
  rw [cocycle_pullback] at hncap
  change absoluteChain (TopCat.of (P' × Q')) n k (n + k) rfl
      (CompactJoinCocycle.cocycle (α.comp f) (β.comp g) hn hρ) ≫ (push (input f g)).f k =
    (push (input f g)).f (n + k) ≫ absoluteChain (TopCat.of (P × Q)) n k (n + k) rfl
      (CompactJoinCocycle.cocycle α β hn hρ) at hncap
  rw [Category.assoc, CompactJoinCapLocalization.source, ← Category.assoc,
    ← HomologicalComplex.comp_f, smallMap_source, HomologicalComplex.comp_f]
  rw [Category.assoc, ← hncap, ← Category.assoc]
  rw [← CompactJoinCapLocalization.source (α.comp f) (β.comp g) hn hρ hρR k]
  simp only [Category.assoc]
  rw [hj]

theorem localized_homology (k : ℕ) :
    HomologicalComplex.homologyMap (smallMap α β f g ρ) (n + k) ≫
      (CompactJoinCapLocalization.localized α β hn hρ hρR).homology k =
    (CompactJoinCapLocalization.localized (α.comp f) (β.comp g) hn hρ hρR).homology k ≫
      HomologicalComplex.homologyMap (push (nearMap α β f g R)) k := by
  rw [← DegreeLoweringHomology.Map.pre_homology, ← DegreeLoweringHomology.Map.post_homology]
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro q
  exact component α β f g hn hρ hρR q

theorem unrefined_homology (k : ℕ) : HomologicalComplex.homologyMap (push (input f g)) (n + k) ≫
    (CompactJoinCapLocalization.unrefined α β hn hρ hρR).homology k =
    (CompactJoinCapLocalization.unrefined (α.comp f) (β.comp g) hn hρ hρR).homology k ≫
      HomologicalComplex.homologyMap (push (nearMap α β f g R)) k := by
  have hr := SmallRetractionHomology.homology_naturality
    (CompactJoinCapLocalization.cover (α.comp f) (β.comp g) ρ) (CompactJoinCapLocalization.cover α β ρ)
    (CompactJoinCapLocalization.cover_open (α.comp f) (β.comp g) ρ) (CompactJoinCapLocalization.cover_univ (α.comp f) (β.comp g) hρ)
    (CompactJoinCapLocalization.cover_open α β ρ) (CompactJoinCapLocalization.cover_univ α β hρ)
    (input f g) (fun i => (f i.1, g i.2)) (cover_maps α β f g ρ) (n + k)
  have hcmap := localized_homology α β f g hn hρ hρR k
  rw [CompactJoinCapLocalization.unrefined, CompactJoinCapLocalization.unrefined,
    DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology]
  dsimp only [smallMap, SmallRetractionComparison.map, push] at hcmap ⊢
  rw [← Category.assoc, ← hr, Category.assoc, hcmap, ← Category.assoc]

end
end Finsler.CompactJoinCapNaturality
