module

public import Finsler.Topology.ClosedCapDegreeTransport

/-! The actual nested-to-annular degree transport commutes with chain
maps before or after the cap. These identities preserve the specified
source approximations rather than replacing them by homology classes. -/

@[expose] public section
namespace Finsler.ClosedCapFunctoriality

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem transport_f {K C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ C) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg K.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg C.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem align_pre {K C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ C) (m p : ℕ) (u : ∀ q, C.X ((m + 1) + (p + q)) ⟶ D.X q) (q : ℕ) :
    ClosedCapDegreeTransport.align m p (fun s => f.f ((m + 1) + (p + s)) ≫ u s) q =
      f.f ((m + p) + q + 1) ≫ ClosedCapDegreeTransport.align m p u q := by
  dsimp only [ClosedCapDegreeTransport.align]
  rw [← Category.assoc, transport_f f ((m + p) + q + 1) ((m + 1) + (p + q)) (by omega), Category.assoc]

theorem align_post {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : D ⟶ E) (m p : ℕ) (u : ∀ q, C.X ((m + 1) + (p + q)) ⟶ D.X q) (q : ℕ) :
    ClosedCapDegreeTransport.align m p (fun s => u s ≫ f.f s) q =
      ClosedCapDegreeTransport.align m p u q ≫ f.f q := by
  dsimp only [ClosedCapDegreeTransport.align]
  exact (Category.assoc _ _ _).symm

end
end Finsler.ClosedCapFunctoriality
