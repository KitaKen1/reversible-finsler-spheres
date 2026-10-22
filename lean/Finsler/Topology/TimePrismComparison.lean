module

public import Finsler.Topology.TimePrismDescent
public import Finsler.Topology.DegreeLoweringExact

/-! A relative cochain homotopy survives the time prism when its actual
endpoint restrictions vanish. The source time cylinder need not be a cycle. -/

@[expose] public section
namespace Finsler.TimePrismComparison

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
  {g₀ g₁ : C ⟶ D} (H : Homotopy g₀ g₁)

theorem cycles_prism_boundary (j : ℕ) :
    (C.iCycles j ≫ H.hom j (j + 1)) ≫ D.d (j + 1) j =
      C.iCycles j ≫ (g₀.f j - g₁.f j) := by
  cases j with
  | zero =>
    have h := congrArg (fun f => C.iCycles 0 ≫ f) (H.comm 0)
    simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
      zero_add, Preadditive.comp_add, ← Category.assoc] at h
    exact (eq_sub_iff_add_eq.mpr h.symm).trans (Preadditive.comp_sub _ _ _).symm
  | succ j =>
    have h := congrArg (fun f => C.iCycles (j + 1) ≫ f) (H.comm (j + 1))
    simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
      Preadditive.comp_add, ← Category.assoc, C.iCycles_d, zero_comp, zero_add] at h
    exact (eq_sub_iff_add_eq.mpr h.symm).trans (Preadditive.comp_sub _ _ _).symm

variable (d : ℕ)
  (u v : ∀ q, D.X (d + q + 1) ⟶ E.X q)
  (k : ∀ q, D.X (d + q) ⟶ E.X q)

theorem cycle_boundary
    (hk : ∀ q, k (q + 1) ≫ E.d (q + 1) q =
      D.d (d + q + 1) (d + q) ≫ k q - (u q - v q))
    (h₀ : ∀ q, g₀.f (d + q) ≫ k q = 0)
    (h₁ : ∀ q, g₁.f (d + q) ≫ k q = 0) (q : ℕ) :
    C.iCycles (d + q) ≫
        (H.hom (d + q) (d + q + 1) ≫ u q - H.hom (d + q) (d + q + 1) ≫ v q) =
      (C.iCycles (d + q) ≫
        (-(H.hom (d + q) (d + q + 1) ≫ k (q + 1)))) ≫ E.d (q + 1) q := by
  have h := congrArg (fun f => (C.iCycles (d + q) ≫
    H.hom (d + q) (d + q + 1)) ≫ f) (hk q)
  have hz : ((C.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1)) ≫
      D.d (d + q + 1) (d + q)) ≫ k q = 0 := by
    rw [cycles_prism_boundary, Category.assoc, Preadditive.sub_comp,
      h₀ q, h₁ q, sub_self, comp_zero]
  simp only [Preadditive.comp_sub, ← Category.assoc] at h
  rw [hz, zero_sub] at h
  have hn := congrArg Neg.neg h
  simpa only [Preadditive.comp_sub, Preadditive.comp_neg, Preadditive.neg_comp,
    neg_neg, Category.assoc] using hn.symm

theorem homology_eq
    (hk : ∀ q, k (q + 1) ≫ E.d (q + 1) q =
      D.d (d + q + 1) (d + q) ≫ k q - (u q - v q))
    (h₀ : ∀ q, g₀.f (d + q) ≫ k q = 0)
    (h₁ : ∀ q, g₁.f (d + q) ≫ k q = 0)
    (f g : DegreeLoweringHomology.Map C E d)
    (hf : ∀ q, f.component q = H.hom (d + q) (d + q + 1) ≫ u q)
    (hg : ∀ q, g.component q = H.hom (d + q) (d + q + 1) ≫ v q) (q : ℕ) :
    f.homology q = g.homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary f g q
    (-(H.hom (d + q) (d + q + 1) ≫ k (q + 1)))
  rw [hf, hg]
  exact cycle_boundary H d u v k hk h₀ h₁ q

end
end Finsler.TimePrismComparison
