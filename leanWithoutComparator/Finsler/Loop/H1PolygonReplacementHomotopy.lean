module

public import Finsler.Loop.CompactContinuousLoopPolygon
public import Finsler.Topology.SupportedCapNaturality

/-! On an ACTUAL energy-bounded H1 family, the literal ordinary-family
polygon replacement using the SAME segments and subdivision is the
endpoint of the EXISTING genuine strong-H1 Milnor homotopy. -/

@[expose] public section
namespace Finsler.H1PolygonReplacementHomotopy
open CategoryTheory AlgebraicTopology TopologicalSpace Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1200000

variable {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
  (M : PolygonModelData F a N) {X : TopCat.{0}} (u : X ⟶ Loops n)
  (hE : ∀ x, SobolevEnergy.energy F (u x) < a ^ 2)
  (L : Compacts (ContinuousLoopModel.space n))
  (hshort : ∀ v : L, ShortPolygon M.δ (CompactContinuousLoopSampling.sample N v.val))
  (g : X ⟶ TopCat.of L)
  (hg : g ≫ SupportedCap.subspaceMap (ContinuousLoopModel.space n) (L : Set (ContinuousLoopModel.space n)) =
    u ≫ ContinuousLoopModel.inclusion n)

include hg in
theorem replacement_eq (x : X) :
    CompactContinuousLoopPolygon.approximation M.toSegmentData L N hshort (g x) =
      PolygonModel.broken M ⟨PolygonSampling.samplePoly N (u x), PolygonModel.sample_short M (hE x)⟩ := by
  have hx := ConcreteCategory.congr_hom hg x
  change (g x).val = ContinuousLoopModel.inclusion n (u x) at hx
  have hs : CompactContinuousLoopSampling.sample N (g x).val = PolygonSampling.samplePoly N (u x) := by
    rw [hx]
    exact CompactContinuousLoopSampling.sample_H1 n N (u x)
  change ShortPolygonH1Model.broken M.toSegmentData N
      (CompactContinuousLoopPolygon.toPolygon M.toSegmentData L N hshort (g x)) =
    ShortPolygonH1Model.broken M.toSegmentData N ⟨PolygonSampling.samplePoly N (u x), PolygonModel.sample_short M (hE x)⟩
  congr 1
  exact Subtype.ext hs

def homotopy : TopCat.Homotopy u
    (g ≫ CompactContinuousLoopPolygon.approximation M.toSegmentData L N hshort) where
  toFun z := PolygonModel.deform M ((z.1 : ℝ), u z.2)
  continuous_toFun := by
    have hc : Continuous (fun z : _root_.unitInterval × X => ((z.1 : ℝ), u z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk (u.hom.continuous.comp continuous_snd)
    exact (PolygonModel.deform_continuousOn M).comp_continuous hc (fun z => ⟨z.1.property, hE z.2⟩)
  map_zero_left x := PolygonModel.deform_zero M (hE x)
  map_one_left x := (PolygonModel.deform_one M (hE x)).trans (replacement_eq M u hE L hshort g hg x).symm

include hE hg in
theorem homology (q : ℕ) : HomologicalComplex.homologyMap (push u) q =
    HomologicalComplex.homologyMap
      (push (g ≫ CompactContinuousLoopPolygon.approximation M.toSegmentData L N hshort)) q :=
  ((homotopy M u hE L hshort g hg).toSSet.chainComplexMap coeff).homologyMap_eq q

end
end Finsler.H1PolygonReplacementHomotopy
