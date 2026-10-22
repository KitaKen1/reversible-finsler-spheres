module

public import Finsler.Loop.FilteredThomSupportRadius
public import Finsler.Loop.DegreeLoweringComposition

/-! The actual filtered self-cut time is literally first Thom time
followed by the existing closed tested cap. All degree casts are kept;
this allows a radius comparison before the tested cochain is introduced. -/

@[expose] public section
namespace Finsler.FilteredSelfCutTimeFactor

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem hom_transport {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f g : C ⟶ D} (H : Homotopy f g) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ H.hom j (j + 1) =
      H.hom i (i + 1) ≫ eqToHom (congrArg D.X (congrArg (fun x => x + 1) h)) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable (m p : ℕ) (F : ReversibleMetric (m + 1)) {ρ S ε a L : ℝ}
  (hρ : 0 < ρ) (hρS : ρ < S) (hS : S ≤ 1) (hε : 0 < ε)
  (hSS : S ≤ SelfCutLengthControl.radius F hε)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0)

def testedMap := (FilteredTestedCap.operation F hS hε hSS p T hT hshort).pre
  (push (FilteredPrismSelfCut.toIncoming F S a))

def composed := DegreeLoweringComposition.compose (FilteredThomSupportRadius.operation m F a hρ hρS)
  (testedMap m p F hS hε hSS T hT hshort)

theorem component (q : ℕ) :
    (composed m p F hρ hρS hS hε hSS T hT hshort).component q =
    (FilteredPrismSelfCut.operation m p F hρ hρS hS hε hSS T hT hshort (a := a)).component q := by
  rw [composed, DegreeLoweringComposition.component]
  change eqToHom (congrArg (chains (TopCat.of (SelfCutOscillation.short F a))).X (Nat.add_assoc m p q)) ≫
    (((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom (m + (p + q)) (m + (p + q) + 1) ≫
      eqToHom (congrArg (chains (FilteredPrismSelfCut.domain F a)).X
        (show m + (p + q) + 1 = (m + 1) + (p + q) by omega)) ≫
        (FilteredPrismSelfCut.firstThom (by omega) F a hρ hρS).component (p + q)) ≫
      ((push (FilteredPrismSelfCut.toIncoming F S a)).f (p + q) ≫
        (FilteredTestedCap.operation F hS hε hSS p T hT hshort).component q) =
    ((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom ((m + p) + q) (((m + p) + q) + 1) ≫
      eqToHom (congrArg (chains (FilteredPrismSelfCut.domain F a)).X
        (show ((m + p) + q) + 1 = (m + 1) + (p + q) by omega)) ≫
        (FilteredPrismSelfCut.firstThom (by omega) F a hρ hρS).component (p + q) ≫
          (push (FilteredPrismSelfCut.toIncoming F S a)).f (p + q) ≫
            (FilteredTestedCap.operation F hS hε hSS p T hT hshort).component q
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom _ _),
    hom_transport]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  omega

theorem homology (q : ℕ) :
    (composed m p F hρ hρS hS hε hSS T hT hshort).homology q =
    (FilteredPrismSelfCut.operation m p F hρ hρS hS hε hSS T hT hshort (a := a)).homology q :=
  DegreeLoweringHomology.Map.homology_eq_of_components _ _
    (component m p F hρ hρS hS hε hSS T hT hshort) q

end
end Finsler.FilteredSelfCutTimeFactor
