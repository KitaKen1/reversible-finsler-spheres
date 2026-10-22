module

public import Finsler.Topology.TimePrismComparison

/-! A homotopy of maps out of the time cylinder compares capped time
operations. Its two side prisms must vanish after the actual cap. The
explicit double prism gives the output boundary, including degree zero. -/

@[expose] public section
namespace Finsler.TimeCylinderComparison

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C D E F : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
  {g₀ g₁ : C ⟶ D} {f g : D ⟶ E} (H : Homotopy g₀ g₁) (J : Homotopy f g)
  (d : ℕ) (u : ∀ q, E.X (d + q + 1) ⟶ F.X q)

theorem cycle_boundary
    (hu : ∀ q, u (q + 1) ≫ F.d (q + 1) q =
      E.d (d + q + 2) (d + q + 1) ≫ u q)
    (h₀ : ∀ q, g₀.f (d + q) ≫ (J.hom (d + q) (d + q + 1) ≫ u q) = 0)
    (h₁ : ∀ q, g₁.f (d + q) ≫ (J.hom (d + q) (d + q + 1) ≫ u q) = 0) (q : ℕ) :
    (C.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1)) ≫
        ((f.f (d + q + 1) - g.f (d + q + 1)) ≫ u q) =
      (C.iCycles (d + q) ≫ (H.hom (d + q) (d + q + 1) ≫
        J.hom (d + q + 1) (d + q + 2) ≫ u (q + 1))) ≫ F.d (q + 1) q := by
  have hj : f.f (d + q + 1) - g.f (d + q + 1) =
      D.d (d + q + 1) (d + q) ≫ J.hom (d + q) (d + q + 1) +
      J.hom (d + q + 1) (d + q + 2) ≫ E.d (d + q + 2) (d + q + 1) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
      J.comm (d + q + 1)
  have hs : (C.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1)) ≫
      ((D.d (d + q + 1) (d + q) ≫ J.hom (d + q) (d + q + 1)) ≫ u q) = 0 := by
    calc
      _ = ((C.iCycles (d + q) ≫ H.hom (d + q) (d + q + 1)) ≫
          D.d (d + q + 1) (d + q)) ≫ (J.hom (d + q) (d + q + 1) ≫ u q) := by
        simp only [Category.assoc]
      _ = C.iCycles (d + q) ≫
          ((g₀.f (d + q) - g₁.f (d + q)) ≫ (J.hom (d + q) (d + q + 1) ≫ u q)) := by
        rw [TimePrismComparison.cycles_prism_boundary, Category.assoc]
      _ = 0 := by
        rw [Preadditive.sub_comp, h₀ q, h₁ q, sub_self, comp_zero]
  rw [hj, Preadditive.add_comp, Preadditive.comp_add, hs, zero_add]
  simp only [Category.assoc, hu q]

theorem homology_eq
    (hu : ∀ q, u (q + 1) ≫ F.d (q + 1) q =
      E.d (d + q + 2) (d + q + 1) ≫ u q)
    (h₀ : ∀ q, g₀.f (d + q) ≫ (J.hom (d + q) (d + q + 1) ≫ u q) = 0)
    (h₁ : ∀ q, g₁.f (d + q) ≫ (J.hom (d + q) (d + q + 1) ≫ u q) = 0)
    (a b : DegreeLoweringHomology.Map C F d)
    (ha : ∀ q, a.component q = H.hom (d + q) (d + q + 1) ≫ f.f (d + q + 1) ≫ u q)
    (hb : ∀ q, b.component q = H.hom (d + q) (d + q + 1) ≫ g.f (d + q + 1) ≫ u q)
    (q : ℕ) : a.homology q = b.homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary a b q
    (H.hom (d + q) (d + q + 1) ≫ J.hom (d + q + 1) (d + q + 2) ≫ u (q + 1))
  rw [ha, hb]
  simpa only [Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp] using
    cycle_boundary H J d u hu h₀ h₁ q

end
end Finsler.TimeCylinderComparison
