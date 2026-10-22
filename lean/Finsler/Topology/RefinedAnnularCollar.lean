module

public import Finsler.Topology.AnnularCollarCut
public import Finsler.Topology.CarrierSubspaceFactor

/-! Source subdivision preserves the whole parent image. Consequently
the actual original annular cut still kills every map or time prism
carried by the diagonal collar, after any specified source approximation.
The conclusion passes to genuine filtered lifts by chain monicity. -/

@[expose] public section
namespace Finsler.RefinedAnnularCollar

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem approximation_map_zero {Y Z : TopCat.{0}} {ι : Type*} (U : ι → Set Z)
    (f : Y ⟶ Z) (g : Z ⟶ parameters (m + 1))
    (hf : ∀ y, distance (m + 1) (g (f y)) ≤ δ) (q : ℕ) :
    (push f).f ((m + p) + q + 1) ≫
      (TauCeti.singularSmallApprox coeff U).f ((m + p) + q + 1) ≫
      (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q = 0 := by
  let N := (m + p) + q + 1
  let B : Set (parameters (m + 1)) := {z | distance (m + 1) z ≤ δ}
  have hzero : (push (SupportedCap.subspaceMap (parameters (m + 1)) B)).f N ≫
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
    (approximation_parent U τ)
  rw [← Category.assoc, hσ, ← Category.assoc, ← Category.assoc, ← hc,
    Category.assoc, hzero, comp_zero]
  simp only [comp_zero]

theorem filtered_map_zero {Y Z : TopCat.{0}} {ι : Type*} (U : ι → Set Z)
    (g : Z ⟶ parameters (m + 1)) (B : Set (SphereLoop (m + 1)))
    (v : ∀ q, (chains Z).X ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q)
    (hv : ∀ q, v q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
      (TauCeti.singularSmallApprox coeff U).f ((m + p) + q + 1) ≫
        (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)
    (f : Y ⟶ Z) (hf : ∀ y, distance (m + 1) (g (f y)) ≤ δ) (q : ℕ) :
    (push f).f ((m + p) + q + 1) ≫ v q = 0 := by
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (SphereLoop (m + 1))) B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q)).mp
  rw [zero_comp, Category.assoc, hv]
  exact approximation_map_zero m p h hρr hr T hT U f g hf q

theorem filtered_prism_zero {Y Z : TopCat.{0}} {ι : Type*} (U : ι → Set Z)
    (g : Z ⟶ parameters (m + 1)) (B : Set (SphereLoop (m + 1)))
    (v : ∀ q, (chains Z).X ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q)
    (hv : ∀ q, v q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
      (TauCeti.singularSmallApprox coeff U).f ((m + p) + q + 1) ≫
        (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)
    {f₀ f₁ : Y ⟶ Z} (H : TopCat.Homotopy f₀ f₁)
    (hH : ∀ z, distance (m + 1) (g (H.h z)) ≤ δ) (q : ℕ) :
    (H.toSSet.chainComplexMap coeff).hom ((m + p) + q) ((m + p) + q + 1) ≫ v q = 0 := by
  rw [← TimeShuffleComparison.rectangle_eq_prism]
  unfold TimeShuffleComparison.rectangle
  rw [Category.assoc, filtered_map_zero m p h hρr hr T hT U g B v hv H.h hH q, comp_zero]

end
end Finsler.RefinedAnnularCollar
