module

public import Finsler.Topology.SmallCapCarrier
public import Finsler.Topology.SmallInclusionHomologyCancellation
public import Finsler.Topology.SupportedCapHomology

/-! The actual global closed cap and small-chain retraction commute
on homology with the small complex as the target. Both restrictions
to genuine small inputs agree literally, and the actual input
homology section removes that restriction. No target injectivity is
used. This controls the first global join cap, not unclosed extensions. -/

@[expose] public section
namespace Finsler.SmallCapRetractionHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set X)
  (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ)
  (a : ℕ) (φ : singularCochainGroup (ZMod 2) X a)
  (hφ : cochainCoboundary (ZMod 2) X a φ = 0)

def absolute : DegreeLoweringHomology.Map (chains X) (chains X) a :=
  SupportedCapHomology.absoluteOperation X a φ hφ

def smallCap : DegreeLoweringHomology.Map (small X U) (small X U) a where
  component q := SmallCapCarrier.smallCap X U a q (a + q) rfl φ
  comm q := by
    letI : Mono ((inclusion X U).f q) :=
      inferInstanceAs (Mono ((sigmaConst.obj coeff).map
        ((X.smallSingularSubcomplex U).ι.app (Opposite.op ⦋q⦌))))
    apply (cancel_mono ((inclusion X U).f q)).mp
    rw [Category.assoc, ← (inclusion X U).comm, ← Category.assoc,
      SmallCapCarrier.smallCap_inclusion, Category.assoc]
    have hb := (SupportedCapHomology.absoluteOperation X a φ hφ).comm q
    change absoluteChain X a (q + 1) (a + (q + 1)) rfl φ ≫ (chains X).d (q + 1) q =
      (chains X).d (a + (q + 1)) (a + q) ≫ absoluteChain X a q (a + q) rfl φ at hb
    rw [hb, ← Category.assoc, (inclusion X U).comm, Category.assoc,
      ← SmallCapCarrier.smallCap_inclusion]
    exact (Category.assoc _ _ _).symm

def before : DegreeLoweringHomology.Map (chains X) (small X U) a :=
  (smallCap X U a φ hφ).pre (smallSingularRetraction (X := X) coeff U hU hc)

def after : DegreeLoweringHomology.Map (chains X) (small X U) a :=
  (absolute X a φ hφ).post (smallSingularRetraction (X := X) coeff U hU hc)

theorem before_pre_component (q : ℕ) :
    ((before X U hU hc a φ hφ).pre (inclusion X U)).component q =
      (smallCap X U a φ hφ).component q := by
  dsimp only [before, DegreeLoweringHomology.Map.pre]
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    ι_comp_smallSingularRetraction coeff U hU hc, HomologicalComplex.id_f, Category.id_comp]

theorem after_pre_component (q : ℕ) :
    ((after X U hU hc a φ hφ).pre (inclusion X U)).component q =
      (smallCap X U a φ hφ).component q := by
  dsimp only [after, absolute, SupportedCapHomology.absoluteOperation, smallCap,
    DegreeLoweringHomology.Map.pre, DegreeLoweringHomology.Map.post]
  rw [← Category.assoc, ← SmallCapCarrier.smallCap_inclusion,
    Category.assoc, ← HomologicalComplex.comp_f,
    ι_comp_smallSingularRetraction coeff U hU hc, HomologicalComplex.id_f, Category.comp_id]

theorem homology_eq (q : ℕ) :
    (before X U hU hc a φ hφ).homology q = (after X U hU hc a φ hφ).homology q := by
  apply SmallInclusionHomologyCancellation.homology_eq X U hU hc (small X U) a
    (before X U hU hc a φ hφ) (after X U hU hc a φ hφ) q
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro t
  rw [before_pre_component, after_pre_component]

end
end Finsler.SmallCapRetractionHomology
