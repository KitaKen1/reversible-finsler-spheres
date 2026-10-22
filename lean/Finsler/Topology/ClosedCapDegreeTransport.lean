module

public import Finsler.Topology.DegreeLoweringHomology

/-! Transport the actual two-cochain input degree to the original
annular cut convention, preserving both boundary and ambient inclusion
identities. This supplies the small filtered caps used by time prisms. -/

@[expose] public section
namespace Finsler.ClosedCapDegreeTransport

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem transport_d (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i j i' j' : ℕ) (hi : i = i') (hj : j = j') :
    eqToHom (congrArg C.X hi) ≫ C.d i' j' = C.d i j ≫ eqToHom (congrArg C.X hj) := by
  subst i'
  subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j ≫ eqToHom (congrArg D.X h.symm) = f.f i := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (m p : ℕ)
  (u : ∀ q, C.X ((m + 1) + (p + q)) ⟶ D.X q)

def align (q : ℕ) : C.X ((m + p) + q + 1) ⟶ D.X q :=
  eqToHom (congrArg C.X (show (m + p) + q + 1 = (m + 1) + (p + q) by omega)) ≫ u q

theorem align_comm (hu : ∀ q, u (q + 1) ≫ D.d (q + 1) q =
    C.d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ u q) (q : ℕ) :
    align m p u (q + 1) ≫ D.d (q + 1) q =
      C.d ((m + p) + q + 2) ((m + p) + q + 1) ≫ align m p u q := by
  have ht := transport_d C ((m + p) + q + 2) ((m + p) + q + 1)
    ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) (by omega) (by omega)
  dsimp [align]
  rw [Category.assoc, hu q, ← Category.assoc, ht]
  simp only [Category.assoc]

theorem align_inclusion {E F : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (i : D ⟶ E) (f : C ⟶ F)
    (c : ∀ q, F.X ((m + p) + q + 1) ⟶ E.X q)
    (hi : ∀ q, u q ≫ i.f q = f.f ((m + 1) + (p + q)) ≫
      eqToHom (congrArg F.X (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫ c q) (q : ℕ) :
    align m p u q ≫ i.f q = f.f ((m + p) + q + 1) ≫ c q := by
  dsimp [align]
  rw [Category.assoc, hi q]
  simpa only [Category.assoc] using congrArg (fun g => g ≫ c q)
    (transport_f f ((m + p) + q + 1) ((m + 1) + (p + q)) (by omega))

end
end Finsler.ClosedCapDegreeTransport
