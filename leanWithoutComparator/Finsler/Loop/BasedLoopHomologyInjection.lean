module

public import Finsler.Loop.BasedCompactPolygon

/-! The ACTUAL H1-to-ordinary based-loop inclusion is injective on
singular homology in every degree. Use a compact genuine null-class
factorization and the same actual based polygon replacement on its
source. No based-loop homology calculation is assumed. -/
@[expose] public section
namespace Finsler.BasedLoopHomologyInjection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Topology TopologicalSpace
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.H1LocalFiber (based)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem compact_energy_bound {n : ℕ} (y : Sphere n) (F : ReversibleMetric n)
    (K : Compacts (TopCat.of (based y))) :
    ∃ a : ℝ, ∀ u : K, SobolevEnergy.energy F u.val.val < a ^ 2 := by
  let J : Compacts (Loops n) :=
    ⟨(fun u : based y => u.val) '' (K : Set (based y)), K.isCompact.image continuous_subtype_val⟩
  obtain ⟨a, hE⟩ := H1LoopHomologyInjection.compact_energy_bound F J
  exact ⟨a, fun u => hE ⟨u.val.val, u.val, u.property, rfl⟩⟩

theorem kernel_zero {n : ℕ} (y : Sphere n) (q : ℕ) (z : (chains (TopCat.of (based y))).homology q)
    (hz : (HomologicalComplex.homologyMap (push (BasedContinuousLoopModel.inclusion y)) q).hom z = 0) :
    z = 0 := by
  obtain ⟨K, w, hw⟩ := CompactHomologyLift.exists_lift (TopCat.of (based y)) q z
  let u := SupportedCap.subspaceMap (TopCat.of (based y)) (K : Set (based y))
  have hKw : (HomologicalComplex.homologyMap (push (u ≫ BasedContinuousLoopModel.inclusion y)) q).hom w = 0 := by
    rw [push_comp, HomologicalComplex.homologyMap_comp]
    change (HomologicalComplex.homologyMap (push (BasedContinuousLoopModel.inclusion y)) q).hom
      ((HomologicalComplex.homologyMap (push u) q).hom w) = 0
    rw [hw]
    exact hz
  obtain ⟨L, g, hg, hzero⟩ := CompactMapZeroFactor.exists_factor
    (BasedContinuousLoopModel.inclusion y) K q w hKw
  let F := Geometry.roundMetric n
  obtain ⟨S⟩ := PolygonModel.exists_segmentData F
  obtain ⟨a, hE⟩ := compact_energy_bound y F K
  obtain ⟨Ne, he⟩ := PolygonSampling.exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨Nc, hc, hs⟩ := CompactContinuousLoopSampling.exists_short_samples
    (BasedCompactPolygon.ambientCompact y L) S.pos
  let N := max Ne Nc
  have hN : 0 < N := hc.trans_le (le_max_right _ _)
  let : NeZero N := ⟨hN.ne'⟩
  let M : PolygonModelData F a N := PolygonModelData.mk S (he N (le_max_left _ _) hN)
  have hshort : ∀ v : BasedCompactPolygon.ambientCompact y L,
      PolygonLoop.ShortPolygon M.δ (CompactContinuousLoopSampling.sample N v.val) := hs N (le_max_right _ _)
  have hh := BasedCompactPolygon.homology y M u hE L hshort g hg q
  rw [← hw, hh, push_comp, HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap
    (push (BasedCompactPolygon.approximation y M.toSegmentData L N hshort)) q).hom
      ((HomologicalComplex.homologyMap (push g) q).hom w) = 0
  rw [hzero, map_zero]

theorem homology_injective {n : ℕ} (y : Sphere n) (q : ℕ) : Function.Injective
    (HomologicalComplex.homologyMap (push (BasedContinuousLoopModel.inclusion y)) q).hom := by
  intro a b h
  apply sub_eq_zero.mp
  apply kernel_zero y q (a - b)
  rw [map_sub, h, sub_self]

theorem zero_of_ordinary_zero {n : ℕ} (y : Sphere n) (q : ℕ)
    (ho : IsZero (homologyZMod2 (BasedContinuousLoopModel.space y) q)) :
    IsZero (homologyZMod2 (TopCat.of (based y)) q) := by
  have hs := ModuleCat.subsingleton_of_isZero ho
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun a b => homology_injective y q (hs.elim _ _)⟩

end
end Finsler.BasedLoopHomologyInjection
