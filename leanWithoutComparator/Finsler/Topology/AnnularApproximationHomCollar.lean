module

public import Finsler.Topology.RefinedAnnularCollar
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! The actual approximation homotopy preserves each whole parent.
Its capped endpoint terms therefore vanish for the original annular
cut whenever the original endpoint image lies in the diagonal collar. -/

@[expose] public section
namespace Finsler.AnnularApproximationHomCollar
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem endpoint_zero (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    {Y Z : TopCat.{0}} {ι : Type*} (U : ι → Set Z)
    (f : Y ⟶ Z) (g : Z ⟶ parameters (m + 1))
    (hf : ∀ y, distance (m + 1) (g (f y)) ≤ δ) (q : ℕ) :
    (push f).f ((m + p) + q) ≫
      (singularSmallApproxHomotopy (X := Z) coeff U).hom ((m + p) + q) ((m + p) + q + 1) ≫
      (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q = 0 := by
  let N := (m + p) + q
  change (push f).f N ≫ singularSmallApproxHom coeff U N (N + 1) ≫
    (push g).f (N + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q = 0
  let B : Set (parameters (m + 1)) := {z | distance (m + 1) z ≤ δ}
  have hzero : (push (SupportedCap.subspaceMap (parameters (m + 1)) B)).f (N + 1) ≫
      AnnularCutComparison.cut m p h hρr hr T hT q = 0 :=
    AnnularCollarCut.cut_map_zero_of_distance m p h hρr hr T hT q _ (fun z => z.property)
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  let τ := (TopCat.toSSet.map f).app _ σ
  have hσ : (TopCat.toSSet.obj Y).ιChainComplex σ ≫ (push f).f N =
      (TopCat.toSSet.obj Z).ιChainComplex τ := by
    dsimp [N, τ]
    simp only [push, SSet.ι_chainComplexMap_f]
  have hparent : ∀ center, Set.MapsTo g (parentFamily.{1} τ center) B := by
    intro center
    change Set.MapsTo g (Set.range (Z.toSSetObjEquiv _ τ)) B
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨t, rfl⟩
    exact hf ((Y.toSSetObjEquiv _ σ) t)
  obtain ⟨c, hc⟩ := CarrierSubspaceFactor.push_factor (parentFamily.{1} τ) g B hparent
    (approximationPrism_parent U τ)
  rw [← Category.assoc, hσ, ← Category.assoc, ← Category.assoc, ← hc,
    Category.assoc, hzero, comp_zero]
  simp only [comp_zero]

end
end Finsler.AnnularApproximationHomCollar
