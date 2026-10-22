module

public import Finsler.Topology.SmallRefinementComparison
public import Finsler.Topology.PullbackPairCover
public import Finsler.Topology.TimeCylinderComparison
public import Finsler.Topology.SmallInclusionHomologyCancellation
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! Actual relative time comparison under a source-cover refinement.
Both endpoints become small on one genuine input cover. The concrete
refinement homotopy vanishes there, so its capped double prism fills
the difference in the very same output complex, including degree zero. -/

@[expose] public section
namespace Finsler.TimeCoverRefinementComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1100000

variable {Z : TopCat.{0}} {ι κ : Type*} (U : ι → Set Z) (V : κ → Set Z)
  (r : ι → κ) (href : ∀ i, U i ⊆ V (r i))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)

theorem small_zero (i j : ℕ) : (inclusion Z U).f i ≫
    (SmallRefinementComparison.comparison U V r href hU hcU hV hcV).hom i j = 0 := by
  change (inclusion Z U).f i ≫ (0 +
    (singularSmallApproxHom coeff U i j ≫ (smallSingularRetraction (X := Z) coeff V hV hcV).f j + 0)) = 0
  rw [zero_add, add_zero, ← Category.assoc, ι_comp_singularSmallApproxHom, zero_comp]

theorem homology_eq (X : TopCat.{0}) (f₀ f₁ : X ⟶ Z)
    (H : Homotopy (push f₀) (push f₁))
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (u : ∀ q, (small Z V).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small Z V).d (d + q + 2) (d + q + 1) ≫ u q)
    (a b : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, a.component q = H.hom (d + q) (d + q + 1) ≫
      (smallSingularRetraction (X := Z) coeff V hV hcV).f (d + q + 1) ≫ u q)
    (hb : ∀ q, b.component q = H.hom (d + q) (d + q + 1) ≫
      (smallSingularRetraction (X := Z) coeff U hU hcU ≫
        SmallRefinementComparison.refinement U V r href).f (d + q + 1) ≫ u q) (q : ℕ) :
    a.homology q = b.homology q := by
  let S := PullbackPairCover.cover (X := X) U U f₀ f₁
  let j := inclusion X S
  let H' := H.compLeft j
  let J := SmallRefinementComparison.comparison U V r href hU hcU hV hcV
  let e₀ := PullbackPairCover.leftMap (X := X) U U f₀ f₁
  let e₁ := PullbackPairCover.rightMap (X := X) U U f₀ f₁
  have he₀ : j ≫ push f₀ = e₀ ≫ inclusion Z U :=
    (PullbackPairCover.leftMap_inclusion (X := X) U U f₀ f₁).symm
  have he₁ : j ≫ push f₁ = e₁ ≫ inclusion Z U :=
    (PullbackPairCover.rightMap_inclusion (X := X) U U f₀ f₁).symm
  have hz₀ (t : ℕ) : (j ≫ push f₀).f (d + t) ≫ (J.hom (d + t) (d + t + 1) ≫ u t) = 0 := by
    rw [he₀, HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ((inclusion Z U).f (d + t)),
      small_zero U V r href hU hcU hV hcV, zero_comp, comp_zero]
  have hz₁ (t : ℕ) : (j ≫ push f₁).f (d + t) ≫ (J.hom (d + t) (d + t + 1) ≫ u t) = 0 := by
    rw [he₁, HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ((inclusion Z U).f (d + t)),
      small_zero U V r href hU hcU hV hcV, zero_comp, comp_zero]
  apply SmallInclusionHomologyCancellation.homology_eq X S
    (PullbackPairCover.isOpen (X := X) U U f₀ f₁ hU hU)
    (PullbackPairCover.covers (X := X) U U f₀ f₁ hcU hcU) E d a b q
  apply TimeCylinderComparison.homology_eq H' J d u hu hz₀ hz₁ (a.pre j) (b.pre j)
  · intro t
    simp only [DegreeLoweringHomology.Map.pre, ha, H', Homotopy.compLeft_hom, Category.assoc]
  · intro t
    simp only [DegreeLoweringHomology.Map.pre, hb, H', Homotopy.compLeft_hom, Category.assoc]

end
end Finsler.TimeCoverRefinementComparison
