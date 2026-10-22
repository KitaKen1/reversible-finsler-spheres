module

public import Finsler.Loop.TimeCoverRefinementComparison
public import Finsler.Topology.RelativeSmallRetraction

/-! Actual relative time comparison for retraction naturality between
*different* ambient spaces. Both endpoints become genuinely small on
one input cover; the resulting double prism stays in the specified
filtered cap target. No time cylinder is assumed to be a cycle. -/

@[expose] public section
namespace Finsler.TimeMappedRetractionComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {Z Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set Z) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)
  (f : Z ⟶ Y) (r : ι → κ) (href : ∀ i, Set.MapsTo f (U i) (V (r i)))

theorem homology_eq (X : TopCat.{0}) (f₀ f₁ : X ⟶ Z)
    (H : Homotopy (push f₀) (push f₁))
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (u : ∀ q, (small Y V).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small Y V).d (d + q + 2) (d + q + 1) ≫ u q)
    (a b : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, a.component q = H.hom (d + q) (d + q + 1) ≫
      (push f ≫ smallSingularRetraction (X := Y) coeff V hV hcV).f (d + q + 1) ≫ u q)
    (hb : ∀ q, b.component q = H.hom (d + q) (d + q + 1) ≫
      (smallSingularRetraction (X := Z) coeff U hU hcU ≫
        SmallRetractionComparison.map U V f r href).f (d + q + 1) ≫ u q) (q : ℕ) :
    a.homology q = b.homology q := by
  let S := PullbackPairCover.cover (X := X) U U f₀ f₁
  let j := inclusion X S
  let H' := H.compLeft j
  let J := SmallRetractionComparison.comparison U V hU hcU hV hcV f r href
  let e₀ := PullbackPairCover.leftMap (X := X) U U f₀ f₁
  let e₁ := PullbackPairCover.rightMap (X := X) U U f₀ f₁
  have he₀ : j ≫ push f₀ = e₀ ≫ inclusion Z U :=
    (PullbackPairCover.leftMap_inclusion (X := X) U U f₀ f₁).symm
  have he₁ : j ≫ push f₁ = e₁ ≫ inclusion Z U :=
    (PullbackPairCover.rightMap_inclusion (X := X) U U f₀ f₁).symm
  have hz₀ (t : ℕ) : (j ≫ push f₀).f (d + t) ≫ (J.hom (d + t) (d + t + 1) ≫ u t) = 0 := by
    rw [he₀, HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ((inclusion Z U).f (d + t)),
      RelativeSmallRetraction.small_zero U V hU hcU hV hcV f r href, zero_comp, comp_zero]
  have hz₁ (t : ℕ) : (j ≫ push f₁).f (d + t) ≫ (J.hom (d + t) (d + t + 1) ≫ u t) = 0 := by
    rw [he₁, HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ((inclusion Z U).f (d + t)),
      RelativeSmallRetraction.small_zero U V hU hcU hV hcV f r href, zero_comp, comp_zero]
  apply SmallInclusionHomologyCancellation.homology_eq X S
    (PullbackPairCover.isOpen (X := X) U U f₀ f₁ hU hU)
    (PullbackPairCover.covers (X := X) U U f₀ f₁ hcU hcU) E d a b q
  apply TimeCylinderComparison.homology_eq H' J d u hu hz₀ hz₁ (a.pre j) (b.pre j)
  · intro t
    simp only [DegreeLoweringHomology.Map.pre, ha, H', Homotopy.compLeft_hom, Category.assoc]
  · intro t
    simp only [DegreeLoweringHomology.Map.pre, hb, H', Homotopy.compLeft_hom, Category.assoc]

end
end Finsler.TimeMappedRetractionComparison
