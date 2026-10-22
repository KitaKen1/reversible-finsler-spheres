module

public import Finsler.Topology.SupportedCapNaturality

/-! Transport genuine cap source diagrams between equal native input
degrees, keeping the actual chain map and output fixed. -/

@[expose] public section
namespace Finsler.CapSourceDegreeTransport
open CategoryTheory
noncomputable section
set_option autoImplicit false

variable {K C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {E : ModuleCat.{0} (ZMod 2)}
  (f : K ⟶ C) (i j l : ℕ) (hij : i = j) (hil : i = l) (hjl : j = l)
  (u : K.X j ⟶ E) (z : C.X l ⟶ E)

theorem pre (hu : u = f.f j ≫ eqToHom (congrArg C.X hjl) ≫ z) :
    eqToHom (congrArg K.X hij) ≫ u = f.f i ≫ eqToHom (congrArg C.X hil) ≫ z := by
  cases hij
  simpa only [eqToHom_refl, Category.id_comp] using hu

theorem rebase (hu : eqToHom (congrArg K.X hij) ≫ u = f.f i ≫ eqToHom (congrArg C.X hil) ≫ z) :
    u = f.f j ≫ eqToHom (congrArg C.X hjl) ≫ z := by
  cases hij
  simpa only [eqToHom_refl, Category.id_comp] using hu

end
end Finsler.CapSourceDegreeTransport
