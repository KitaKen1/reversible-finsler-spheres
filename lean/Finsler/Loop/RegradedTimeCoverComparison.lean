module

public import Finsler.Loop.TimeCoverRefinementComparison
public import Finsler.Topology.DegreeLoweringSuccAlignment

/-! The real cover-refinement time comparison with an arbitrary native
cap degree equal to the time degree plus one. -/

@[expose] public section
namespace Finsler.RegradedTimeCoverComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

theorem normal {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (d N : ℕ) (hN : d + 1 = N)
    (c : DegreeLoweringHomology.Map D E N) (q : ℕ) :
    eqToHom (congrArg C.X (show d + q + 1 = N + q by omega)) ≫ f.f (N + q) ≫ c.component q =
      f.f (d + q + 1) ≫ DegreeLoweringSuccAlignment.align d c hN.symm q := by
  simpa only [DegreeLoweringSuccAlignment.align, DegreeLoweringHomology.Map.pre] using
    DegreeLoweringSuccAlignment.pre d c hN.symm f q

theorem homology_eq {Z : TopCat.{0}} {ι κ : Type*} (U : ι → Set Z) (V : κ → Set Z)
    (r : ι → κ) (href : ∀ i, U i ⊆ V (r i))
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)
    (X : TopCat.{0}) (f₀ f₁ : X ⟶ Z) (H : Homotopy (push f₀) (push f₁))
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d N : ℕ) (hN : d + 1 = N)
    (c : DegreeLoweringHomology.Map (small Z V) E N)
    (a b : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, a.component q = H.hom (d + q) (d + q + 1) ≫
      eqToHom (congrArg (chains Z).X (show d + q + 1 = N + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := Z) coeff V hV hcV).f (N + q) ≫ c.component q)
    (hb : ∀ q, b.component q = H.hom (d + q) (d + q + 1) ≫
      eqToHom (congrArg (chains Z).X (show d + q + 1 = N + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU ≫
        SmallRefinementComparison.refinement U V r href).f (N + q) ≫ c.component q)
    (q : ℕ) : a.homology q = b.homology q := by
  apply TimeCoverRefinementComparison.homology_eq U V r href hU hcU hV hcV X f₀ f₁ H E d
    (DegreeLoweringSuccAlignment.align d c hN.symm) (DegreeLoweringSuccAlignment.comm d c hN.symm)
  · intro t
    rw [ha]
    simpa only [Category.assoc] using congrArg (fun k => H.hom (d + t) (d + t + 1) ≫ k)
      (normal (TauCeti.smallSingularRetraction (X := Z) coeff V hV hcV) d N hN c t)
  · intro t
    rw [hb]
    simpa only [Category.assoc] using congrArg (fun k => H.hom (d + t) (d + t + 1) ≫ k)
      (normal (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU ≫
        SmallRefinementComparison.refinement U V r href) d N hN c t)

end
end Finsler.RegradedTimeCoverComparison
