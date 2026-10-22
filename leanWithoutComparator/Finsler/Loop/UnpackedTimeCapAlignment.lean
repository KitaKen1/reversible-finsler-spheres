module

public import Finsler.Loop.TimeCapCompositionAlignment
public import Finsler.Loop.NestedCapUnpack

/-! The exact time alignment of a real closed flat cap after a
source retraction, expressed in its genuine nested degree convention. -/

@[expose] public section
namespace Finsler.UnpackedTimeCapAlignment

open CategoryTheory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem aligned {C S E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (R : C ⟶ S) (m p : ℕ) (c : DegreeLoweringHomology.Map S E ((m + 1) + p)) (q : ℕ) :
    DegreeLoweringSuccAlignment.align (m + p) (c.pre R) (by omega) q =
    ClosedCapDegreeTransport.align m p
      (fun t => R.f ((m + 1) + (p + t)) ≫ NestedCapUnpack.component (m + 1) p c t) q := by
  dsimp only [DegreeLoweringSuccAlignment.align, DegreeLoweringHomology.Map.pre,
    ClosedCapDegreeTransport.align, NestedCapUnpack.component]
  rw [← Category.assoc (R.f ((m + 1) + (p + q))),
    ← transport_f R ((m + 1) + (p + q)) (((m + 1) + p) + q) (Nat.add_assoc (m + 1) p q).symm]
  simp only [← Category.assoc, eqToHom_trans]

end
end Finsler.UnpackedTimeCapAlignment
