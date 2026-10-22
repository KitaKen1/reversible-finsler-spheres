module

public import Finsler.Topology.NativeAnnularTimeComparison

/-! Every genuine filtered model with the actual prescribed time
component has the native original annular operation as its ambient
homology image. Identify actual parameter maps before comparing the
original full loop operation, with no filtered homology injectivity. -/

@[expose] public section
namespace Finsler.FilteredModelNativeComparison
open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 400000

variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (X Z : TopCat.{0}) {ι : Type*} (U : ι → Set Z) (g : Z ⟶ parameters (m + 1))
  (f : TopCat.of (ClosedInterval × X) ⟶ Z)
  (h₀ : ∀ x, distance (m + 1) (g (f (0, x))) ≤ δ)
  (h₁ : ∀ x, distance (m + 1) (g (f (1, x))) ≤ δ)
  (B : Set (SphereLoop (m + 1)))
  (v : ∀ q, (chains Z).X ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q)
  (hv : ∀ q, v q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
    (singularSmallApprox (X := Z) coeff U).f ((m + p) + q + 1) ≫
      (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)
  (a : DegreeLoweringHomology.Map (chains X) (chains (TopCat.of B)) (m + p))
  (ha : ∀ q, a.component q = AnnularTimeTrim.prism X ((m + p) + q) ≫
    (push f).f ((m + p) + q + 1) ≫ v q)

include hv ha h₀ h₁

theorem model_inclusion (q : ℕ) :
    a.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
      (AnnularTrimHomology.operation (X := X) m p h hρr hr T hT (f ≫ g) h₀ h₁).homology q := by
  let j := push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)
  change a.homology q ≫ HomologicalComplex.homologyMap j q = _
  rw [← a.post_homology j q]
  symm
  apply NativeAnnularTimeComparison.native_model_homology_eq m p h hρr hr T hT X Z U g f h₀ h₁ (a.post j) ?_ q
  intro q
  change a.component q ≫ j.f q = _
  rw [ha q]
  simp only [j, Category.assoc, hv]

theorem identified_inclusion
    (e : TopCat.of (ClosedInterval × X) ⟶ parameters (m + 1)) (he : f ≫ g = e)
    (he₀ : ∀ x, distance (m + 1) (e (0, x)) ≤ δ)
    (he₁ : ∀ x, distance (m + 1) (e (1, x)) ≤ δ) (q : ℕ) :
    a.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
      (AnnularTrimHomology.operation (X := X) m p h hρr hr T hT e he₀ he₁).homology q := by
  have hm := model_inclusion m p h hρr hr T hT X Z U g f h₀ h₁ B v hv a ha q
  refine hm.trans ?_
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro q
  change AnnularTimeTrim.component m p h hρr hr T hT (f ≫ g) q =
    AnnularTimeTrim.component m p h hρr hr T hT e q
  rw [he]

theorem full_inclusion
    (u : C(X, SphereLoop (m + 1))) (he : f ≫ g = AnnularSelfCut.familyMap u) (q : ℕ) :
    a.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
      ((AnnularCutComparison.operation m p h hρr hr T hT).pre (push (TopCat.ofHom u))).homology q := by
  have hm := model_inclusion m p h hρr hr T hT X Z U g f h₀ h₁ B v hv a ha q
  refine hm.trans ?_
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro q
  change AnnularTimeTrim.component m p h hρr hr T hT (f ≫ g) q =
    (push (TopCat.ofHom u)).f ((m + p) + q) ≫ (AnnularCutComparison.operation m p h hρr hr T hT).component q
  rw [he]
  exact AnnularTimeTrim.full_component m p h hρr hr T hT u q

end
end Finsler.FilteredModelNativeComparison
