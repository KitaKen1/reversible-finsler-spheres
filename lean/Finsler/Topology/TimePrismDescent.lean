module

public import Finsler.Topology.DegreeLoweringHomology
public import Finsler.Topology.BorelCochain
public import Mathlib.Algebra.Homology.Homotopy

/-! Composing a genuine time prism with a closed degree-lowering operation
whose two endpoint restrictions vanish. The resulting operation lowers the
degree by one less, including output degree zero. -/

@[expose] public section
namespace Finsler.TimePrismDescent

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
  {g₀ g₁ : C ⟶ D} (H : Homotopy g₀ g₁) (d : ℕ)
  (u : ∀ q, D.X (d + q + 1) ⟶ E.X q)

def component (q : ℕ) : C.X (d + q) ⟶ E.X q :=
  H.hom (d + q) (d + q + 1) ≫ u q

theorem component_boundary
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      D.d (d + q + 2) (d + q + 1) ≫ u q)
    (h₀ : ∀ q, g₀.f (d + q + 1) ≫ u q = 0)
    (h₁ : ∀ q, g₁.f (d + q + 1) ≫ u q = 0) (q : ℕ) :
    component H d u (q + 1) ≫ E.d (q + 1) q =
      C.d (d + (q + 1)) (d + q) ≫ component H d u q := by
  have h := congrArg (fun k => k ≫ u q) (H.comm (d + q + 1))
  simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
    Preadditive.add_comp, Category.assoc, h₀ q, h₁ q, add_zero] at h
  have he : C.d (d + q + 1) (d + q) ≫
      (H.hom (d + q) (d + q + 1) ≫ u q) =
    H.hom (d + q + 1) (d + q + 2) ≫
      (D.d (d + q + 2) (d + q + 1) ≫ u q) := by
    apply add_right_cancel (b := H.hom (d + q + 1) (d + q + 2) ≫
      (D.d (d + q + 2) (d + q + 1) ≫ u q))
    exact h.symm.trans (BorelCochain.two_eq_zero_of_mod _).symm
  unfold component
  rw [Category.assoc, hu q]
  exact he.symm

def operation
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      D.d (d + q + 2) (d + q + 1) ≫ u q)
    (h₀ : ∀ q, g₀.f (d + q + 1) ≫ u q = 0)
    (h₁ : ∀ q, g₁.f (d + q + 1) ≫ u q = 0) :
    DegreeLoweringHomology.Map C E d where
  component := component H d u
  comm := component_boundary H d u hu h₀ h₁

end
end Finsler.TimePrismDescent
