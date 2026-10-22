module

public import Finsler.Topology.SelfCutEndpoints
public import Finsler.Topology.SelfCutTimePrism
public import Finsler.Topology.TimePrismDescent

/-! The actual normalized self-cut composed with the genuine time-cylinder
prism, as a degree-(n+p-1)-lowering chain operation. Comparison with the
specified shuffled time rectangle and whole-parent length control remain. -/

@[expose] public section
namespace Finsler.PrismSelfCut

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

private theorem cast_d (D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    {i i' j j' : ℕ} (hi : i = i') (hj : j = j') :
    eqToHom (congrArg D.X hi) ≫ D.d i' j' =
      D.d i j ≫ eqToHom (congrArg D.X hj) := by
  subst i'
  subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem map_cast {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) {i j : ℕ} (h : i = j) :
    f.f i ≫ eqToHom (congrArg D.X h) = eqToHom (congrArg C.X h) ≫ f.f j := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable (m p : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def cut (q : ℕ) :
    (chains (parameters (m + 1))).X ((m + p) + q + 1) ⟶
      (chains (TopCat.of (SphereLoop (m + 1)))).X q :=
  eqToHom (congrArg (chains (parameters (m + 1))).X
    (by omega : (m + p) + q + 1 = (m + 1) + (p + q))) ≫
      NormalizedSelfCut.chainCut (m + 1) p (by omega) hρ hρr hr T hT q

theorem cut_boundary (q : ℕ) :
    cut m p hρ hρr hr T hT (q + 1) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q =
      (chains (parameters (m + 1))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
        cut m p hρ hρr hr T hT q := by
  unfold cut
  rw [Category.assoc, NormalizedSelfCut.chainCut_boundary, ← Category.assoc,
    cast_d _ (j := (m + p) + q + 1) (by omega) (by omega), Category.assoc]
  rfl

theorem cut_time_zero (q : ℕ) :
    (SupportedCapNaturality.push (atTime (m + 1) 0)).f ((m + p) + q + 1) ≫
      cut m p hρ hρr hr T hT q = 0 := by
  unfold cut
  rw [← Category.assoc, map_cast _ (by omega), Category.assoc,
    SelfCutEndpoints.chainCut_time_zero, comp_zero]

theorem cut_time_one (q : ℕ) :
    (SupportedCapNaturality.push (atTime (m + 1) 1)).f ((m + p) + q + 1) ≫
      cut m p hρ hρr hr T hT q = 0 := by
  unfold cut
  rw [← Category.assoc, map_cast _ (by omega), Category.assoc,
    SelfCutEndpoints.chainCut_time_one, comp_zero]

def operation : DegreeLoweringHomology.Map
    (chains (TopCat.of (SphereLoop (m + 1))))
    (chains (TopCat.of (SphereLoop (m + 1)))) (m + p) :=
  TimePrismDescent.operation (SelfCutTimePrism.chainHomotopy (m + 1)) (m + p)
    (cut m p hρ hρr hr T hT) (cut_boundary m p hρ hρr hr T hT)
    (cut_time_zero m p hρ hρr hr T hT) (cut_time_one m p hρ hρr hr T hT)

theorem operation_boundary (q : ℕ) :
    (operation m p hρ hρr hr T hT).component (q + 1) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q =
      (chains (TopCat.of (SphereLoop (m + 1)))).d ((m + p) + (q + 1)) ((m + p) + q) ≫
        (operation m p hρ hρr hr T hT).component q :=
  (operation m p hρ hρr hr T hT).comm q

theorem cycles_closed (q : ℕ) :
    ((chains (TopCat.of (SphereLoop (m + 1)))).iCycles ((m + p) + q) ≫
      (operation m p hρ hρr hr T hT).component q) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d q (q - 1) = 0 :=
  (operation m p hρ hρr hr T hT).cycles_closed q

end
end Finsler.PrismSelfCut
