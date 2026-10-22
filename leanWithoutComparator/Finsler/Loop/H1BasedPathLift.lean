module

public import Finsler.Loop.BasedContinuousLoopModel
public import Finsler.Loop.H1BasedPolygonHomotopy
public import Finsler.Loop.H1LoopHomologyInjection

/-! An actual path of ordinary based loops lifts, after one common
polygon subdivision, to an actual path between the original strong-H1
based loops. Genuine Milnor endpoint paths retain the same basepoint. -/
@[expose] public section
namespace Finsler.H1BasedPathLift
open CategoryTheory Topology TopologicalSpace
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.CompactH1Alignment Finsler.H1BasedPolygonHomotopy
open Finsler.H1LocalFiber (based)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem approximation_eq {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (M : PolygonModelData F a N) (u : SphereLoop n) (hu : SobolevEnergy.energy F u < a ^ 2)
    (K : Compacts (ContinuousLoopModel.space n))
    (hshort : ∀ v : K, ShortPolygon M.δ (CompactContinuousLoopSampling.sample N v.val))
    (p : K) (hp : p.val = ContinuousLoopModel.inclusion n u) :
    CompactContinuousLoopPolygon.approximation M.toSegmentData K N hshort p =
      PolygonModel.broken M ⟨samplePoly N u, PolygonModel.sample_short M hu⟩ := by
  have hs : CompactContinuousLoopSampling.sample N p.val = samplePoly N u := by
    rw [hp]
    exact CompactContinuousLoopSampling.sample_H1 n N u
  change ShortPolygonH1Model.broken M.toSegmentData N
    (CompactContinuousLoopPolygon.toPolygon M.toSegmentData K N hshort p) =
      ShortPolygonH1Model.broken M.toSegmentData N ⟨samplePoly N u, PolygonModel.sample_short M hu⟩
  congr 1
  exact Subtype.ext hs

theorem joined_of_ordinary_joined {n : ℕ} (y : Sphere n) (u v : based y)
    (h : Joined (BasedContinuousLoopModel.inclusion y u) (BasedContinuousLoopModel.inclusion y v)) :
    Joined u v := by
  obtain ⟨γ⟩ := h
  let K : Compacts (ContinuousLoopModel.space n) :=
    ⟨Set.range (fun t : _root_.unitInterval => (γ t).val),
      isCompact_range (continuous_subtype_val.comp γ.continuous)⟩
  let g : C(_root_.unitInterval, K) :=
    ⟨fun t => ⟨(γ t).val, ⟨t, rfl⟩⟩, (continuous_subtype_val.comp γ.continuous).subtype_mk _⟩
  let F := Geometry.roundMetric n
  let a := |SobolevEnergy.energy F u.val| + |SobolevEnergy.energy F v.val| + 1
  have hu : SobolevEnergy.energy F u.val < a ^ 2 := by
    dsimp [a]
    nlinarith [abs_nonneg (SobolevEnergy.energy F u.val), abs_nonneg (SobolevEnergy.energy F v.val),
      le_abs_self (SobolevEnergy.energy F u.val),
      sq_nonneg (|SobolevEnergy.energy F u.val| + |SobolevEnergy.energy F v.val|)]
  have hv : SobolevEnergy.energy F v.val < a ^ 2 := by
    dsimp [a]
    nlinarith [abs_nonneg (SobolevEnergy.energy F u.val), abs_nonneg (SobolevEnergy.energy F v.val),
      le_abs_self (SobolevEnergy.energy F v.val),
      sq_nonneg (|SobolevEnergy.energy F u.val| + |SobolevEnergy.energy F v.val|)]
  obtain ⟨S⟩ := PolygonModel.exists_segmentData F
  obtain ⟨Ne, he⟩ := PolygonSampling.exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨Nc, hc, hs⟩ := CompactContinuousLoopSampling.exists_short_samples K S.pos
  let N := max Ne Nc
  have hN : 0 < N := hc.trans_le (le_max_right _ _)
  let : NeZero N := ⟨hN.ne'⟩
  let M : PolygonModelData F a N := PolygonModelData.mk S (he N (le_max_left _ _) hN)
  have hshort : ∀ p : K, ShortPolygon M.δ (CompactContinuousLoopSampling.sample N p.val) :=
    hs N (le_max_right _ _)
  let e := CompactContinuousLoopPolygon.approximation M.toSegmentData K N hshort
  let b : _root_.unitInterval → based y := fun t =>
    ⟨e (g t), (approximation_basepoint M.toSegmentData K N hshort (g t)).trans
      (congrArg Subtype.val (γ t).property)⟩
  have hb : Continuous b := (e.hom.continuous.comp g.continuous).subtype_mk _
  have h₀ : b 0 = replacement y M u hu :=
    Subtype.ext (approximation_eq M u.val hu K hshort (g 0) (congrArg Subtype.val γ.source))
  have h₁ : b 1 = replacement y M v hv :=
    Subtype.ext (approximation_eq M v.val hv K hshort (g 1) (congrArg Subtype.val γ.target))
  have hm : Joined (replacement y M u hu) (replacement y M v hv) := by
    have hj : Joined (b 0) (b 1) := ⟨{ toFun := b, continuous_toFun := hb, source' := rfl, target' := rfl }⟩
    simpa only [h₀, h₁] using hj
  exact (show Joined u (replacement y M u hu) from ⟨H1BasedPolygonHomotopy.path y M u hu⟩).trans
    (hm.trans ⟨(H1BasedPolygonHomotopy.path y M v hv).symm⟩)

def constant {n : ℕ} (y : Sphere n) : based y := ⟨constantSphereLoop y, by
  change (sphereRepresentative (constantSphereLoop y) (0 : ClosedInterval) : Ambient n) = y
  rw [sphereRepresentative_constantSphereLoop]⟩

theorem pathConnected {n : ℕ} (hn : 2 ≤ n) (y : Sphere n) : PathConnectedSpace (based y) := by
  let := BasedContinuousLoopModel.pathConnected hn y
  exact ⟨⟨constant y⟩, fun u v => joined_of_ordinary_joined y u v (PathConnectedSpace.joined _ _)⟩

end
end Finsler.H1BasedPathLift
