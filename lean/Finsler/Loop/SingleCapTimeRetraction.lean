module

public import Finsler.Loop.SingleCapTimeRefinement

/-! Relate the explicit retraction/cap degree convention to the
relative time comparison without discarding either endpoint term. -/

@[expose] public section
namespace Finsler.SingleCapTimeRetraction

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem normal {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (d : ℕ) (c : DegreeLoweringHomology.Map D E (d + 1)) (q : ℕ) :
    eqToHom (congrArg C.X (show d + q + 1 = (d + 1) + q by omega)) ≫
      f.f ((d + 1) + q) ≫ c.component q =
    f.f (d + q + 1) ≫ SingleCapTimeRefinement.aligned d c q := by
  rw [SingleCapTimeRefinement.aligned_normal, ← Category.assoc,
    transport_f f (d + q + 1) ((d + 1) + q) (by omega), Category.assoc]

variable {Z : TopCat.{0}} {ι κ : Type*} (U : ι → Set Z) (V : κ → Set Z)
  (r : ι → κ) (href : ∀ i, U i ⊆ V (r i))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)

theorem homology_eq (X : TopCat.{0}) (f₀ f₁ : X ⟶ Z) (H : Homotopy (push f₀) (push f₁))
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (cU : DegreeLoweringHomology.Map (small Z U) E (d + 1))
    (cV : DegreeLoweringHomology.Map (small Z V) E (d + 1))
    (hc : ∀ q, (SmallRefinementComparison.refinement U V r href).f ((d + 1) + q) ≫
      cV.component q = cU.component q)
    (a b : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, a.component q = H.hom (d + q) (d + q + 1) ≫
      eqToHom (congrArg (chains Z).X (show d + q + 1 = (d + 1) + q by omega)) ≫
        (TauCeti.smallSingularRetraction (X := Z) coeff V hV hcV).f ((d + 1) + q) ≫ cV.component q)
    (hb : ∀ q, b.component q = H.hom (d + q) (d + q + 1) ≫
      eqToHom (congrArg (chains Z).X (show d + q + 1 = (d + 1) + q by omega)) ≫
        (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU).f ((d + 1) + q) ≫ cU.component q)
    (q : ℕ) : a.homology q = b.homology q := by
  apply SingleCapTimeRefinement.homology_eq d U V r href hU hcU hV hcV X f₀ f₁ H cU cV hc a b
  · intro t
    rw [ha]
    simpa only [Category.assoc] using congrArg (fun k => H.hom (d + t) (d + t + 1) ≫ k)
      (normal (TauCeti.smallSingularRetraction (X := Z) coeff V hV hcV) d cV t)
  · intro t
    rw [hb]
    simpa only [Category.assoc] using congrArg (fun k => H.hom (d + t) (d + t + 1) ≫ k)
      (normal (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU) d cU t)

end
end Finsler.SingleCapTimeRetraction
