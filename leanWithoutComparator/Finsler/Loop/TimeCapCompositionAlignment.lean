module

public import Finsler.Loop.DegreeLoweringComposition
public import Finsler.Loop.DegreeLoweringRegrade
public import Finsler.Topology.DegreeLoweringSuccAlignment
public import Finsler.Topology.ClosedCapDegreeTransport

/-! Exact degree normal forms for a first cap followed by a time cap.
All associativity transports are explicit, including output degree zero. -/

@[expose] public section
namespace Finsler.TimeCapCompositionAlignment

open CategoryTheory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 700000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem compose_aligned {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {a b : ℕ}
    (f : DegreeLoweringHomology.Map C D a) (g : DegreeLoweringHomology.Map D E b)
    (d e : ℕ) (hd : a + b = d + 1) (he : b = e + 1) (q : ℕ) :
    DegreeLoweringSuccAlignment.align d (DegreeLoweringComposition.compose f g) hd q =
      eqToHom (congrArg C.X (show d + q + 1 = a + (e + q + 1) by omega)) ≫
        f.component (e + q + 1) ≫ DegreeLoweringSuccAlignment.align e g he q := by
  dsimp only [DegreeLoweringSuccAlignment.align]
  rw [DegreeLoweringComposition.component]
  rw [← Category.assoc (f.component (e + q + 1))
      (eqToHom (congrArg D.X (show e + q + 1 = b + q by omega))) (g.component q),
    DegreeLoweringRegrade.component_transport f (e + q + 1) (b + q) (by omega)]
  simp only [← Category.assoc, eqToHom_trans]

theorem nested_pre_aligned {C S E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (R : C ⟶ S) (m p : ℕ)
    (c : ∀ q, S.X ((m + 1) + (p + q)) ⟶ E.X q)
    (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
      S.d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q) (q : ℕ) :
    DegreeLoweringSuccAlignment.align (m + p) ((NestedCapHomology.operation (m + 1) p c hc).pre R) (by omega) q =
      ClosedCapDegreeTransport.align m p (fun q => R.f ((m + 1) + (p + q)) ≫ c q) q := by
  dsimp only [DegreeLoweringSuccAlignment.align, DegreeLoweringHomology.Map.pre,
    NestedCapHomology.operation, ClosedCapDegreeTransport.align]
  rw [← Category.assoc (R.f (((m + 1) + p) + q))
      (eqToHom (congrArg S.X (Nat.add_assoc (m + 1) p q))) (c q),
    ← transport_f R (((m + 1) + p) + q) ((m + 1) + (p + q)) (Nat.add_assoc (m + 1) p q)]
  simp only [← Category.assoc, eqToHom_trans]

end
end Finsler.TimeCapCompositionAlignment
