module

public import Finsler.Loop.DegreeLoweringComposition
public import Finsler.Loop.DegreeLoweringRegrade
public import Finsler.Topology.NestedCapHomology
public import Finsler.Topology.SuccAlignmentNaturality
public import Finsler.Topology.TimeCylinderComparison

/-! Output maps and equal degree conventions preserve the actual raw
cap and time-prism normal forms. These are literal chain identities;
no injectivity assumption on any output homology map is used. -/

@[expose] public section
namespace Finsler.TimeCapOutputNaturality

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

private theorem map_ext {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f g : DegreeLoweringHomology.Map C E d) (h : ∀ q, f.component q = g.component q) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := funext h
      cases he
      rfl

theorem raw_post_comm {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (a p : ℕ) (c : ∀ q, C.X (a + (p + q)) ⟶ D.X q)
    (hc : ∀ q, c (q + 1) ≫ D.d (q + 1) q = C.d (a + (p + (q + 1))) (a + (p + q)) ≫ c q)
    (j : D ⟶ E) (q : ℕ) :
    (c (q + 1) ≫ j.f (q + 1)) ≫ E.d (q + 1) q =
      C.d (a + (p + (q + 1))) (a + (p + q)) ≫ (c q ≫ j.f q) := by
  rw [Category.assoc, j.comm, ← Category.assoc, hc, Category.assoc]

theorem nested_post {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (a p : ℕ) (c : ∀ q, C.X (a + (p + q)) ⟶ D.X q)
    (hc : ∀ q, c (q + 1) ≫ D.d (q + 1) q = C.d (a + (p + (q + 1))) (a + (p + q)) ≫ c q)
    (j : D ⟶ E) :
    NestedCapHomology.operation a p (fun q => c q ≫ j.f q) (raw_post_comm a p c hc j) =
      (NestedCapHomology.operation a p c hc).post j := by
  apply map_ext
  intro q
  simp only [NestedCapHomology.operation, DegreeLoweringHomology.Map.post, Category.assoc]

theorem compose_post {B C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {a b : ℕ} (f : DegreeLoweringHomology.Map B C a) (g : DegreeLoweringHomology.Map C D b) (j : D ⟶ E) :
    DegreeLoweringComposition.compose f (g.post j) = (DegreeLoweringComposition.compose f g).post j := by
  apply map_ext
  intro q
  simp only [DegreeLoweringComposition.component, DegreeLoweringHomology.Map.post, Category.assoc]

theorem align_regrade {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {k : ℕ}
    (d : ℕ) (f : DegreeLoweringHomology.Map C E k) (k' : ℕ) (hk : k' = k)
    (hm : k = d + 1) (hm' : k' = d + 1) (q : ℕ) :
    DegreeLoweringSuccAlignment.align d (DegreeLoweringRegrade.regrade f k' hk) hm' q =
      DegreeLoweringSuccAlignment.align d f hm q := by
  dsimp only [DegreeLoweringSuccAlignment.align]
  rw [DegreeLoweringRegrade.regrade_component, ← Category.assoc, eqToHom_trans]

theorem raw_align_post {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (m p : ℕ) (c : ∀ q, C.X ((m + 1) + (p + q)) ⟶ D.X q) (j : D ⟶ E) (q : ℕ) :
    ClosedCapDegreeTransport.align m p (fun q => c q ≫ j.f q) q =
      ClosedCapDegreeTransport.align m p c q ≫ j.f q := by
  simp only [ClosedCapDegreeTransport.align, Category.assoc]

theorem time_regrade_component {A B C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : A ⟶ B} (H : Homotopy f₀ f₁) (r : B ⟶ C) {d k : ℕ}
    (u : DegreeLoweringHomology.Map C E k) (hm : k = d + 1)
    (a : DegreeLoweringHomology.Map A E d)
    (ha : ∀ q, a.component q = H.hom (d + q) (d + q + 1) ≫ r.f (d + q + 1) ≫
      DegreeLoweringSuccAlignment.align d u hm q)
    (d' : ℕ) (hd : d' = d) (hm' : k = d' + 1) (q : ℕ) :
    (DegreeLoweringRegrade.regrade a d' hd).component q = H.hom (d' + q) (d' + q + 1) ≫
      r.f (d' + q + 1) ≫ DegreeLoweringSuccAlignment.align d' u hm' q := by
  subst d'
  simpa only [DegreeLoweringRegrade.regrade_component, eqToHom_refl, Category.id_comp] using ha q

end
end Finsler.TimeCapOutputNaturality
