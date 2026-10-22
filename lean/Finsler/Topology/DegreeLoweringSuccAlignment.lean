module

public import Finsler.Topology.DegreeLoweringHomology

/-! Align a closed cap of degree d+1 with a time prism of degree +1.
Keep the chain-group transports explicit, including output degree zero. -/

@[expose] public section
namespace Finsler.DegreeLoweringSuccAlignment

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

private theorem transport_f {K C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ C) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg K.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg C.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_d (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i i' j j' : ℕ) (hi : i = i') (hj : j = j') :
    eqToHom (congrArg C.X hi) ≫ C.d i' j' = C.d i j ≫ eqToHom (congrArg C.X hj) := by
  subst i'; subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {m : ℕ}
  (d : ℕ) (u : DegreeLoweringHomology.Map C E m) (hm : m = d + 1)

def align (q : ℕ) : C.X (d + q + 1) ⟶ E.X q :=
  eqToHom (congrArg C.X (show d + q + 1 = m + q by omega)) ≫ u.component q

theorem comm (q : ℕ) : align d u hm (q + 1) ≫ E.d (q + 1) q =
    C.d (d + q + 2) (d + q + 1) ≫ align d u hm q := by
  have ht := transport_d C (d + q + 2) (m + (q + 1)) (d + q + 1) (m + q)
    (by omega) (by omega)
  dsimp only [align]
  rw [Category.assoc, u.comm, ← Category.assoc, ht, Category.assoc]

theorem pre {K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ C) (q : ℕ) :
    align d (u.pre f) hm q = f.f (d + q + 1) ≫ align d u hm q := by
  dsimp only [align, DegreeLoweringHomology.Map.pre]
  rw [← Category.assoc, transport_f f (d + q + 1) (m + q) (by omega), Category.assoc]

theorem pre_zero {K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ C) (q : ℕ) (hf : f.f (m + q) ≫ u.component q = 0) :
    f.f (d + q + 1) ≫ align d u hm q = 0 := by
  rw [← pre]
  dsimp only [align, DegreeLoweringHomology.Map.pre]
  rw [hf, comp_zero]

end
end Finsler.DegreeLoweringSuccAlignment
