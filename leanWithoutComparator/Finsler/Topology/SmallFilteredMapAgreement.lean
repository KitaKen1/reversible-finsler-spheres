module

public import Finsler.Topology.SmallRetractionComparison

/-! On one actual source refinement, equality of the original parameter
maps implies literal equality of their filtered output lifts. No source
cycle assumption and no homology injectivity is used. -/

@[expose] public section
namespace Finsler.SmallFilteredMapAgreement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem outputs_eq {X Y Z P L : TopCat.{0}} {ι κ μ : Type*}
    (U : ι → Set X) (V : κ → Set Y) (W : μ → Set Z)
    (f : X ⟶ Y) (g : X ⟶ Z) (s : Y ⟶ P) (t : Z ⟶ P)
    (r₀ : ι → κ) (r₁ : ι → μ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r₀ i))) (hg : ∀ i, Set.MapsTo g (U i) (W (r₁ i)))
    (he : f ≫ s = g ≫ t) (B : Set L) (N q : ℕ)
    (c : (chains P).X N ⟶ (chains L).X q)
    (a : (small Y V).X N ⟶ (chains (TopCat.of B)).X q)
    (b : (small Z W).X N ⟶ (chains (TopCat.of B)).X q)
    (ha : a ≫ (push (SupportedCap.subspaceMap L B)).f q = (inclusion Y V).f N ≫ (push s).f N ≫ c)
    (hb : b ≫ (push (SupportedCap.subspaceMap L B)).f q = (inclusion Z W).f N ≫ (push t).f N ≫ c) :
    (SmallRetractionComparison.map U V f r₀ hf).f N ≫ a =
      (SmallRetractionComparison.map U W g r₁ hg).f N ≫ b := by
  haveI : Mono ((push (SupportedCap.subspaceMap L B)).f q) := SupportedCap.subspacePush_mono L B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap L B)).f q)).mp
  rw [Category.assoc, ha, Category.assoc, hb]
  have hm : SmallRetractionComparison.map U V f r₀ hf ≫ inclusion Y V ≫ push s =
      SmallRetractionComparison.map U W g r₁ hg ≫ inclusion Z W ≫ push t := by
    calc
      _ = inclusion X U ≫ push (f ≫ s) := by
        rw [← Category.assoc, SmallRetractionComparison.map_inclusion, Category.assoc, ← push_comp]
      _ = inclusion X U ≫ push (g ≫ t) := by rw [he]
      _ = _ := by
        rw [push_comp, ← Category.assoc, ← SmallRetractionComparison.map_inclusion, Category.assoc]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun f => f.f N ≫ c) hm

end
end Finsler.SmallFilteredMapAgreement
