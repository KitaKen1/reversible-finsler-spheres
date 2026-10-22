module

public import Finsler.Topology.AnnularApproximationHomCollar
public import Finsler.Topology.FilteredTimePrismOperation
public import Finsler.Topology.AnnularTrimHomology
public import Finsler.Topology.TimeCylinderComparison

/-! In ordinary ambient loop homology the actual refined time model
is the native original annular time operation. The explicit double
prism comparison uses the actual approximation homotopy, whose capped
endpoint terms vanish by full parent-image preservation. This does not
assert injectivity of the filtered-target homology inclusion. -/

@[expose] public section
namespace Finsler.NativeAnnularTimeComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
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

theorem native_model_homology_eq
    (b : DegreeLoweringHomology.Map (chains X) (chains (TopCat.of (SphereLoop (m + 1)))) (m + p))
    (hb : ∀ q, b.component q = AnnularTimeTrim.prism X ((m + p) + q) ≫
      (push f).f ((m + p) + q + 1) ≫
      (singularSmallApprox (X := Z) coeff U).f ((m + p) + q + 1) ≫
      (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q) (q : ℕ) :
    (AnnularTrimHomology.operation (X := X) m p h hρr hr T hT (f ≫ g) h₀ h₁).homology q = b.homology q := by
  let c := fun q => (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q
  have hc (q : ℕ) : c (q + 1) ≫ (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q =
      (chains Z).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ c q := by
    dsimp [c]
    rw [Category.assoc, AnnularCutComparison.cut_boundary]
    simpa only [Nat.add_succ, Nat.add_zero, Category.assoc] using
      congrArg (fun k => k ≫ AnnularCutComparison.cut m p h hρr hr T hT q)
        ((push g).comm ((m + p) + q + 2) ((m + p) + q + 1))
  let H : Homotopy (push (AnnularTimeTrim.slice X 0) ≫ push f)
      (push (AnnularTimeTrim.slice X 1) ≫ push f) :=
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).compRight (push f)
  let J := singularSmallApproxHomotopy (X := Z) coeff U
  have he₀ (q : ℕ) : (push (AnnularTimeTrim.slice X 0) ≫ push f).f ((m + p) + q) ≫
      (J.hom ((m + p) + q) ((m + p) + q + 1) ≫ c q) = 0 := by
    simpa only [J, c, push_comp, HomologicalComplex.comp_f, Category.assoc] using
      AnnularApproximationHomCollar.endpoint_zero m p h hρr hr T hT U
        (AnnularTimeTrim.slice X 0 ≫ f) g h₀ q
  have he₁ (q : ℕ) : (push (AnnularTimeTrim.slice X 1) ≫ push f).f ((m + p) + q) ≫
      (J.hom ((m + p) + q) ((m + p) + q + 1) ≫ c q) = 0 := by
    simpa only [J, c, push_comp, HomologicalComplex.comp_f, Category.assoc] using
      AnnularApproximationHomCollar.endpoint_zero m p h hρr hr T hT U
        (AnnularTimeTrim.slice X 1 ≫ f) g h₁ q
  apply TimeCylinderComparison.homology_eq H J (m + p) c hc he₀ he₁
    (AnnularTrimHomology.operation (X := X) m p h hρr hr T hT (f ≫ g) h₀ h₁) b ?_ ?_ q
  · intro q
    simp only [H, c, AnnularTrimHomology.operation, AnnularTrimHomology.along,
      TimePrismDescent.operation, TimePrismDescent.component, Homotopy.compRight_hom,
      HomologicalComplex.id_f, Category.id_comp, push_comp, HomologicalComplex.comp_f, Category.assoc]
  · intro q
    simpa only [H, J, c, Homotopy.compRight_hom, AnnularTimeTrim.prism, Category.assoc] using hb q

theorem filtered_inclusion_homology
    (B : Set (SphereLoop (m + 1)))
    (v : ∀ q, (chains Z).X ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q)
    (hv : ∀ q, v q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
      (singularSmallApprox (X := Z) coeff U).f ((m + p) + q + 1) ≫
      (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)
    (hcomm : ∀ q, v (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (chains Z).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ v q) (q : ℕ) :
    (FilteredTimePrismOperation.operation m p h hρr hr T hT X Z U g B v hv f hcomm h₀ h₁).homology q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
      (AnnularTrimHomology.operation (X := X) m p h hρr hr T hT (f ≫ g) h₀ h₁).homology q := by
  let o := FilteredTimePrismOperation.operation m p h hρr hr T hT X Z U g B v hv f hcomm h₀ h₁
  let j := push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)
  change o.homology q ≫ HomologicalComplex.homologyMap j q = _
  rw [← o.post_homology j q]
  symm
  apply native_model_homology_eq m p h hρr hr T hT X Z U g f h₀ h₁ (o.post j) ?_ q
  intro q
  simp only [o, j, DegreeLoweringHomology.Map.post, FilteredTimePrismOperation.operation,
    TimePrismDescent.operation, TimePrismDescent.component, FilteredTimePrismOperation.along,
    AnnularTimeTrim.prism, Category.assoc, hv]

end
end Finsler.NativeAnnularTimeComparison
