module

public import Finsler.Loop.LiftedCapCochainBoundary

/-! Precompose the full, nonclosed cap boundary identity by a genuine
chain map, keeping the coboundary term and its degree transport. -/

@[expose] public section
namespace Finsler.CapCochainBoundaryPre

open CategoryTheory AlgebraicTopology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

private theorem transport_f {K D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg K.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem pre {K D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ D) (d : ℕ)
    (c : ∀ q, D.X (d + q) ⟶ E.X q)
    (cδ : ∀ q, D.X ((d + 1) + q) ⟶ E.X q)
    (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
      D.d (d + (q + 1)) (d + q) ≫ c q -
      eqToHom (congrArg D.X (show d + (q + 1) = (d + 1) + q by omega)) ≫ cδ q)
    (q : ℕ) :
    (f.f (d + (q + 1)) ≫ c (q + 1)) ≫ E.d (q + 1) q =
      K.d (d + (q + 1)) (d + q) ≫ (f.f (d + q) ≫ c q) -
      eqToHom (congrArg K.X (show d + (q + 1) = (d + 1) + q by omega)) ≫
        (f.f ((d + 1) + q) ≫ cδ q) := by
  rw [Category.assoc, hc q, Preadditive.comp_sub]
  have ht := transport_f f (d + (q + 1)) ((d + 1) + q) (by omega)
  rw [← Category.assoc, f.comm, Category.assoc]
  rw [← Category.assoc (f.f (d + (q + 1))), ← ht, Category.assoc]

end
end Finsler.CapCochainBoundaryPre
