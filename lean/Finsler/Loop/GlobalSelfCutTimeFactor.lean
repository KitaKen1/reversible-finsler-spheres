module

public import Finsler.Loop.GlobalThomTime
public import Finsler.Loop.DegreeLoweringComposition

/-! Factor the original global time self-cut through first-Thom time
and the actual tested cap, retaining its native degree transports. -/

@[expose] public section
namespace Finsler.GlobalSelfCutTimeFactor
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

private theorem hom_transport {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f g : C ⟶ D} (H : Homotopy f g) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ H.hom j (j + 1) =
      H.hom i (i + 1) ≫ eqToHom (congrArg D.X (congrArg (fun x => x + 1) h)) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable (m p : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def composed := DegreeLoweringComposition.compose (GlobalThomTime.operation m hρ hρr)
  (NormalizedSelfCut.testedOperation (m + 1) p hr T hT)

theorem component (q : ℕ) : (composed m p hρ hρr hr T hT).component q =
    (PrismSelfCut.operation m p hρ hρr hr T hT).component q := by
  rw [composed, DegreeLoweringComposition.component]
  change eqToHom (congrArg (chains (TopCat.of (SphereLoop (m + 1)))).X (Nat.add_assoc m p q)) ≫
    ((SelfCutTimePrism.chainHomotopy (m + 1)).hom (m + (p + q)) (m + (p + q) + 1) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
        (show m + (p + q) + 1 = (m + 1) + (p + q) by omega)) ≫
        (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + q)) ≫
      (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q =
    (SelfCutTimePrism.chainHomotopy (m + 1)).hom ((m + p) + q) (((m + p) + q) + 1) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
        (show ((m + p) + q) + 1 = (m + 1) + (p + q) by omega)) ≫
        (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + q) ≫
          (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) ((SelfCutTimePrism.chainHomotopy (m + 1)).hom _ _), hom_transport]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  omega

theorem homology (q : ℕ) : (composed m p hρ hρr hr T hT).homology q =
    (PrismSelfCut.operation m p hρ hρr hr T hT).homology q :=
  DegreeLoweringHomology.Map.homology_eq_of_components _ _ (component m p hρ hρr hr T hT) q

end
end Finsler.GlobalSelfCutTimeFactor
