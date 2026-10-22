module

public import Finsler.Loop.SingleCapTimePrism
public import Finsler.Loop.TimeCoverRefinementComparison

/-! A genuine relative time-prism comparison for closed single-cap
lifts that agree on a real cover refinement. Endpoint corrections are
handled by the existing relative double-prism theorem. -/

@[expose] public section
namespace Finsler.SingleCapTimeRefinement

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

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

variable {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)

def aligned (c : DegreeLoweringHomology.Map C E (d + 1)) (q : ℕ) : C.X (d + q + 1) ⟶ E.X q :=
  ClosedCapDegreeTransport.align d 0 (NestedCapUnpack.component (d + 1) 0 c) q

theorem aligned_normal (c : DegreeLoweringHomology.Map C E (d + 1)) (q : ℕ) :
    aligned d c q = eqToHom (congrArg C.X (show d + q + 1 = (d + 1) + q by omega)) ≫ c.component q := by
  dsimp only [aligned, ClosedCapDegreeTransport.align, NestedCapUnpack.component]
  rw [← Category.assoc, eqToHom_trans]

theorem aligned_comm (c : DegreeLoweringHomology.Map C E (d + 1)) (q : ℕ) :
    aligned d c (q + 1) ≫ E.d (q + 1) q = C.d (d + q + 2) (d + q + 1) ≫ aligned d c q :=
  ClosedCapDegreeTransport.align_comm d 0 _ (NestedCapUnpack.comm (d + 1) 0 c) q

theorem aligned_refinement (c : DegreeLoweringHomology.Map C E (d + 1))
    (e : DegreeLoweringHomology.Map D E (d + 1)) (f : C ⟶ D)
    (hc : ∀ q, f.f ((d + 1) + q) ≫ e.component q = c.component q) (q : ℕ) :
    f.f (d + q + 1) ≫ aligned d e q = aligned d c q := by
  rw [aligned_normal, aligned_normal, ← Category.assoc,
    ← transport_f f (d + q + 1) ((d + 1) + q) (by omega), Category.assoc, hc]

variable {Z : TopCat.{0}} {ι κ : Type*} (U : ι → Set Z) (V : κ → Set Z)
  (r : ι → κ) (href : ∀ i, U i ⊆ V (r i))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)

theorem homology_eq (X : TopCat.{0}) (f₀ f₁ : X ⟶ Z) (H : Homotopy (push f₀) (push f₁))
    (cU : DegreeLoweringHomology.Map (small Z U) E (d + 1))
    (cV : DegreeLoweringHomology.Map (small Z V) E (d + 1))
    (hc : ∀ q, (SmallRefinementComparison.refinement U V r href).f ((d + 1) + q) ≫
      cV.component q = cU.component q)
    (a b : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, a.component q = H.hom (d + q) (d + q + 1) ≫
      (TauCeti.smallSingularRetraction (X := Z) coeff V hV hcV).f (d + q + 1) ≫ aligned d cV q)
    (hb : ∀ q, b.component q = H.hom (d + q) (d + q + 1) ≫
      (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcU).f (d + q + 1) ≫ aligned d cU q)
    (q : ℕ) : a.homology q = b.homology q := by
  apply TimeCoverRefinementComparison.homology_eq U V r href hU hcU hV hcV X f₀ f₁ H E d
    (aligned d cV) (aligned_comm d cV) a b ha
  intro t
  rw [hb, ← aligned_refinement d cU cV (SmallRefinementComparison.refinement U V r href) hc]
  simp only [HomologicalComplex.comp_f, Category.assoc]

end
end Finsler.SingleCapTimeRefinement
