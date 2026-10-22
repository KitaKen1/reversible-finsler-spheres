module

public import Finsler.Loop.H1BasedPathLift

/-! Concrete compact ordinary-based families have actual strong-H1
polygon replacements in the SAME based fiber. On bounded original H1
families, the actual based Milnor homotopy reaches these replacements. -/
@[expose] public section
namespace Finsler.BasedCompactPolygon
open CategoryTheory AlgebraicTopology Topology TopologicalSpace
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.CompactH1Alignment Finsler.H1BasedPolygonHomotopy
open Finsler.H1LocalFiber (based)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def ambient {n : ℕ} (y : Sphere n) : BasedContinuousLoopModel.space y ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def ambientCompact {n : ℕ} (y : Sphere n) (K : Compacts (BasedContinuousLoopModel.space y)) :
    Compacts (ContinuousLoopModel.space n) :=
  ⟨ambient y '' (K : Set (BasedContinuousLoopModel.space y)), K.isCompact.image (ambient y).hom.continuous⟩

def toAmbientCompact {n : ℕ} (y : Sphere n) (K : Compacts (BasedContinuousLoopModel.space y)) :
    TopCat.of K ⟶ TopCat.of (ambientCompact y K) :=
  TopCat.ofHom ⟨fun u => ⟨u.val.val, u.val, u.property, rfl⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def approximation {n : ℕ} {F : ReversibleMetric n} (y : Sphere n) (S : SegmentData F)
    (K : Compacts (BasedContinuousLoopModel.space y)) (N : ℕ) [NeZero N]
    (hshort : ∀ v : ambientCompact y K, ShortPolygon S.δ (CompactContinuousLoopSampling.sample N v.val)) :
    TopCat.of K ⟶ TopCat.of (based y) :=
  TopCat.ofHom ⟨fun u =>
    ⟨CompactContinuousLoopPolygon.approximation S (ambientCompact y K) N hshort (toAmbientCompact y K u),
      (approximation_basepoint S (ambientCompact y K) N hshort (toAmbientCompact y K u)).trans
        (congrArg Subtype.val u.val.property)⟩,
    ((CompactContinuousLoopPolygon.approximation S (ambientCompact y K) N hshort).hom.continuous.comp
      (toAmbientCompact y K).hom.continuous).subtype_mk _⟩

theorem replacement_eq {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (y : Sphere n) (M : PolygonModelData F a N) {X : TopCat.{0}} (u : X ⟶ TopCat.of (based y))
    (hE : ∀ x, SobolevEnergy.energy F (u x).val < a ^ 2)
    (K : Compacts (BasedContinuousLoopModel.space y))
    (hshort : ∀ v : ambientCompact y K, ShortPolygon M.δ (CompactContinuousLoopSampling.sample N v.val))
    (g : X ⟶ TopCat.of K)
    (hg : g ≫ SupportedCap.subspaceMap (BasedContinuousLoopModel.space y) (K : Set _) =
      u ≫ BasedContinuousLoopModel.inclusion y) (x : X) :
    approximation y M.toSegmentData K N hshort (g x) = replacement y M (u x) (hE x) := by
  apply Subtype.ext
  apply H1BasedPathLift.approximation_eq M (u x).val (hE x) (ambientCompact y K) hshort
    (toAmbientCompact y K (g x))
  have hx := ConcreteCategory.congr_hom hg x
  exact congrArg Subtype.val hx

def homotopy {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (y : Sphere n) (M : PolygonModelData F a N) {X : TopCat.{0}} (u : X ⟶ TopCat.of (based y))
    (hE : ∀ x, SobolevEnergy.energy F (u x).val < a ^ 2)
    (K : Compacts (BasedContinuousLoopModel.space y))
    (hshort : ∀ v : ambientCompact y K, ShortPolygon M.δ (CompactContinuousLoopSampling.sample N v.val))
    (g : X ⟶ TopCat.of K)
    (hg : g ≫ SupportedCap.subspaceMap (BasedContinuousLoopModel.space y) (K : Set _) =
      u ≫ BasedContinuousLoopModel.inclusion y) :
    TopCat.Homotopy u (g ≫ approximation y M.toSegmentData K N hshort) where
  toFun z := ⟨PolygonModel.deform M ((z.1 : ℝ), (u z.2).val),
    (deform_basepoint M (u z.2).val (hE z.2) z.1).trans (u z.2).property⟩
  continuous_toFun := by
    have hc : Continuous (fun z : _root_.unitInterval × X => ((z.1 : ℝ), (u z.2).val)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (u.hom.continuous.comp continuous_snd))
    exact ((PolygonModel.deform_continuousOn M).comp_continuous hc
      (fun z => ⟨z.1.property, hE z.2⟩)).subtype_mk _
  map_zero_left x := Subtype.ext (PolygonModel.deform_zero M (hE x))
  map_one_left x := by
    apply Subtype.ext
    exact (PolygonModel.deform_one M (hE x)).trans
      (congrArg Subtype.val (replacement_eq y M u hE K hshort g hg x)).symm

theorem homology {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (y : Sphere n) (M : PolygonModelData F a N) {X : TopCat.{0}} (u : X ⟶ TopCat.of (based y))
    (hE : ∀ x, SobolevEnergy.energy F (u x).val < a ^ 2)
    (K : Compacts (BasedContinuousLoopModel.space y))
    (hshort : ∀ v : ambientCompact y K, ShortPolygon M.δ (CompactContinuousLoopSampling.sample N v.val))
    (g : X ⟶ TopCat.of K)
    (hg : g ≫ SupportedCap.subspaceMap (BasedContinuousLoopModel.space y) (K : Set _) =
      u ≫ BasedContinuousLoopModel.inclusion y) (q : ℕ) :
    HomologicalComplex.homologyMap (push u) q =
      HomologicalComplex.homologyMap (push (g ≫ approximation y M.toSegmentData K N hshort)) q :=
  ((homotopy y M u hE K hshort g hg).toSSet.chainComplexMap coeff).homologyMap_eq q

end
end Finsler.BasedCompactPolygon
