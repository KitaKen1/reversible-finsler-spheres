module

public import Finsler.Loop.FirstFactorSingularTimeModelComparison
public import Finsler.Topology.SmallCrossNaturality
public import Finsler.Topology.TimePrismDescent
public import Finsler.Topology.TimePrismNaturality

/-! Compare the actual original cylinder with first-factor tensor time.
Every cap lands in the same specified complex; the difference is filled
there by the constructed double prism. Both endpoint zeros are retained. -/

@[expose] public section
namespace Finsler.FirstFactorOriginalTimeComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

def reorder (X Y : TopCat.{0}) : TopCat.of (ClosedInterval × X) ⊗ Y ⟶
    TopCat.of (ClosedInterval × (X × Y)) :=
  TopCat.ofHom ⟨fun z => (z.1.1, (z.1.2, z.2)), by fun_prop⟩

def rightToOriginal (X Y : TopCat.{0}) : X ⊗ TopCat.of (ClosedInterval × Y) ⟶
    TopCat.of (ClosedInterval × (X × Y)) :=
  TopCat.ofHom ⟨fun z => (z.2.1, (z.1, z.2.2)), by fun_prop⟩

theorem slice_square (X Y : TopCat.{0}) (t : ClosedInterval) :
    (AnnularTimeTrim.slice X t ⊗ₘ 𝟙 Y) ≫ reorder X Y = AnnularTimeTrim.slice (X ⊗ Y) t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem reorder_square (X Y : TopCat.{0}) :
    FirstFactorSingularTimeModelComparison.reorder X Y ≫ rightToOriginal X Y = reorder X Y := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem cross_original (X Y : TopCat.{0}) :
    FirstFactorSingularTimeModelComparison.cross X Y ≫ push (rightToOriginal X Y) =
      SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫ push (reorder X Y) := by
  rw [FirstFactorSingularTimeModelComparison.cross, Category.assoc, ← push_comp, reorder_square]

theorem cross_endpoint (X Y : TopCat.{0}) (t : ClosedInterval) :
    (push (AnnularTimeTrim.slice X t) ⊗ₘ 𝟙 (chains Y)) ≫
      (SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫ push (reorder X Y)) =
    SmallRectangleCross.ambient X Y ≫ push (AnnularTimeTrim.slice (X ⊗ Y) t) := by
  have hi : push (𝟙 Y) = 𝟙 (chains Y) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 Y)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [← hi, ← Category.assoc, SmallCrossNaturality.ambient_naturality,
    Category.assoc, ← push_comp, slice_square]

theorem product_prism (X Y : TopCat.{0}) (N : ℕ) :
    ((SingularTimeCylinderMaps.cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) ≫
      (push (rightToOriginal X Y)).f (N + 1) = AnnularTimeTrim.prism (X ⊗ Y) N := by
  let H := TopCat.Homotopy.comp (TopCat.Homotopy.refl (rightToOriginal X Y))
    (SingularTimeCylinderMaps.cylinder X Y)
  have he : H.h = (AnnularTimeTrim.cylinder (X ⊗ Y)).h := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_post (SingularTimeCylinderMaps.cylinder X Y)
    (rightToOriginal X Y) N).trans
      (TimePrismNaturality.prism_congr H (AnnularTimeTrim.cylinder (X ⊗ Y)) he N)

variable (X Y : TopCat.{0}) {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)
  (v : ∀ q, (chains (TopCat.of (ClosedInterval × (X × Y)))).X (d + q + 1) ⟶ E.X q)
  (hv : ∀ q, v (q + 1) ≫ E.d (q + 1) q =
    (chains (TopCat.of (ClosedInterval × (X × Y)))).d (d + q + 2) (d + q + 1) ≫ v q)
  (h₀ : ∀ q, (push (AnnularTimeTrim.slice (X ⊗ Y) 0)).f (d + q + 1) ≫ v q = 0)
  (h₁ : ∀ q, (push (AnnularTimeTrim.slice (X ⊗ Y) 1)).f (d + q + 1) ≫ v q = 0)

def rightCap (q : ℕ) := (push (rightToOriginal X Y)).f (d + q + 1) ≫ v q

include hv in
theorem rightCap_comm (q : ℕ) :
    rightCap X Y d v (q + 1) ≫ E.d (q + 1) q =
    (chains (X ⊗ TopCat.of (ClosedInterval × Y))).d (d + q + 2) (d + q + 1) ≫ rightCap X Y d v q := by
  dsimp only [rightCap]
  rw [Category.assoc, hv, ← Category.assoc]
  change ((push (rightToOriginal X Y)).f (d + q + 2) ≫ _) ≫ _ = _
  rw [(push (rightToOriginal X Y)).comm, Category.assoc]

def tensorCap (q : ℕ) :=
  (SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫ push (reorder X Y)).f
    (d + q + 1) ≫ v q

include hv in
theorem tensorCap_comm (q : ℕ) :
    tensorCap X Y d v (q + 1) ≫ E.d (q + 1) q =
    (chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y).d (d + q + 2) (d + q + 1) ≫
      tensorCap X Y d v q := by
  dsimp only [tensorCap]
  rw [Category.assoc, hv, ← Category.assoc]
  change ((SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫
    push (reorder X Y)).f (d + q + 2) ≫ _) ≫ _ = _
  rw [
    (SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫ push (reorder X Y)).comm,
    Category.assoc]

theorem tensor_endpoint_zero (t : ClosedInterval)
    (ht : ∀ q, (push (AnnularTimeTrim.slice (X ⊗ Y) t)).f (d + q + 1) ≫ v q = 0) (q : ℕ) :
    (push (AnnularTimeTrim.slice X t) ⊗ₘ 𝟙 (chains Y)).f (d + q + 1) ≫ tensorCap X Y d v q = 0 := by
  have he := congrArg (fun f => f.f (d + q + 1)) (cross_endpoint X Y t)
  simpa only [tensorCap, HomologicalComplex.comp_f, Category.assoc, ht q, comp_zero] using
    congrArg (fun f => f ≫ v q) he

def productOperation : DegreeLoweringHomology.Map (chains X ⊗ chains Y) E d :=
  (TimePrismDescent.operation ((AnnularTimeTrim.cylinder (X ⊗ Y)).toSSet.chainComplexMap coeff)
    d v hv h₀ h₁).pre (SmallRectangleCross.ambient X Y)

def tensorOperation : DegreeLoweringHomology.Map (chains X ⊗ chains Y) E d :=
  TimePrismDescent.operation (FullFirstFactorTimePrism.prism X Y) d (tensorCap X Y d v)
    (tensorCap_comm X Y d v hv)
    (tensor_endpoint_zero X Y d v 0 h₀) (tensor_endpoint_zero X Y d v 1 h₁)

theorem homology_eq (q : ℕ) :
    (productOperation X Y d v hv h₀ h₁).homology q =
      (tensorOperation X Y d v hv h₀ h₁).homology q := by
  apply FirstFactorSingularTimeModelComparison.homology_eq X Y d (rightCap X Y d v)
    (rightCap_comm X Y d v hv)
    (productOperation X Y d v hv h₀ h₁) (tensorOperation X Y d v hv h₀ h₁) _ _ q
  · intro q'
    dsimp only [productOperation, DegreeLoweringHomology.Map.pre, TimePrismDescent.operation,
      TimePrismDescent.component, rightCap]
    rw [← Category.assoc (((SingularTimeCylinderMaps.cylinder X Y).toSSet.chainComplexMap coeff).hom _ _),
      product_prism]
    rfl
  · intro q'
    simp only [tensorOperation, TimePrismDescent.operation, TimePrismDescent.component,
      tensorCap, rightCap, ← HomologicalComplex.comp_f, ← Category.assoc, cross_original]

end
end Finsler.FirstFactorOriginalTimeComparison
