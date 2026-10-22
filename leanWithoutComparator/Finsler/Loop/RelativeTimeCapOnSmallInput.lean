module

public import Finsler.Loop.SingleCapTimeRefinement
public import Finsler.Topology.TimeCylinderComparison
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! A relative capped time comparison when the coarse normal form
is known on a genuine input refinement. Both endpoint maps factor
through the fine cylinder cover; the actual double prism stays in E. -/

@[expose] public section
namespace Finsler.RelativeTimeCapOnSmallInput

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem homology_eq (X Z : TopCat.{0}) {ι κ μ : Type*}
    (U : ι → Set Z) (V : κ → Set Z) (r : ι → κ) (href : ∀ i, U i ⊆ V (r i))
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)
    (S : μ → Set X) (hS : ∀ i, IsOpen (S i)) (hcS : ⋃ i, S i = Set.univ)
    (f₀ f₁ : X ⟶ Z) (H : Homotopy (push f₀) (push f₁))
    (e₀ e₁ : small X S ⟶ small Z U)
    (he₀ : inclusion X S ≫ push f₀ = e₀ ≫ inclusion Z U)
    (he₁ : inclusion X S ≫ push f₁ = e₁ ≫ inclusion Z U)
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (cU : DegreeLoweringHomology.Map (small Z U) E (d + 1))
    (cV : DegreeLoweringHomology.Map (small Z V) E (d + 1))
    (hc : ∀ q, (SmallRefinementComparison.refinement U V r href).f ((d + 1) + q) ≫
      cV.component q = cU.component q)
    (a b : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, (inclusion X S).f (d + q) ≫ a.component q =
      (inclusion X S).f (d + q) ≫ H.hom (d + q) (d + q + 1) ≫
        (TauCeti.smallSingularRetraction (X := Z) coeff V hV hcV).f (d + q + 1) ≫
          SingleCapTimeRefinement.aligned d cV q)
    (hb : ∀ q, b.component q = H.hom (d + q) (d + q + 1) ≫
      (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU).f (d + q + 1) ≫
        SingleCapTimeRefinement.aligned d cU q) (q : ℕ) : a.homology q = b.homology q := by
  let j := inclusion X S
  let J := SmallRefinementComparison.comparison U V r href hU hcU hV hcV
  let u := SingleCapTimeRefinement.aligned d cV
  have hz₀ (t : ℕ) : (j ≫ push f₀).f (d + t) ≫ (J.hom (d + t) (d + t + 1) ≫ u t) = 0 := by
    rw [he₀, HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ((inclusion Z U).f (d + t)),
      TimeCoverRefinementComparison.small_zero U V r href hU hcU hV hcV, zero_comp, comp_zero]
  have hz₁ (t : ℕ) : (j ≫ push f₁).f (d + t) ≫ (J.hom (d + t) (d + t + 1) ≫ u t) = 0 := by
    rw [he₁, HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ((inclusion Z U).f (d + t)),
      TimeCoverRefinementComparison.small_zero U V r href hU hcU hV hcV, zero_comp, comp_zero]
  apply SmallInclusionHomologyCancellation.homology_eq X S hS hcS E d a b q
  apply TimeCylinderComparison.homology_eq (H.compLeft j) J d u
    (SingleCapTimeRefinement.aligned_comm d cV) hz₀ hz₁ (a.pre j) (b.pre j)
  · intro t
    simpa only [DegreeLoweringHomology.Map.pre, Homotopy.compLeft_hom, Category.assoc] using ha t
  · intro t
    dsimp only [DegreeLoweringHomology.Map.pre]
    rw [hb,
      ← SingleCapTimeRefinement.aligned_refinement d cU cV (SmallRefinementComparison.refinement U V r href) hc]
    simp only [u, HomologicalComplex.comp_f, Homotopy.compLeft_hom, Category.assoc]

end
end Finsler.RelativeTimeCapOnSmallInput
