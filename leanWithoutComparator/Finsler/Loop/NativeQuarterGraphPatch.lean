module

public import Finsler.Loop.NativeQuarterSupport
public import Finsler.Loop.NativeNorthSupportPatch

/-! Genuine excision of the SAME quarter-radius support through the
already constructed north-meridian chart. The chart and pair map
are actual; shrinking support does not require a global embedding. -/
@[expose] public section
namespace Finsler.NativeQuarterGraphPatch
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates
open Finsler.NativePairRelativeSphereTransport
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def graphGood {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (graphSpace P) :=
  {z | ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 4 ∧
    ‖(z.2.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 4}

abbrev graphPatch {n : ℕ} (P : Sphere n) := NativeNorthSupportPatch.graphPatch P
abbrev nativePatch {n : ℕ} (P : Sphere n) := NativeNorthSupportPatch.nativePatch P

theorem good_preimage {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    sphereCoordinates P ⁻¹' graphGood P v₀ = NativeQuarterSupport.good P v₀ := rfl

theorem close_north {n : ℕ} (P : Sphere n) (v₀ : equator P) (y : Sphere n)
    (hy : ‖(y : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 4) :
    y ∈ MeridianNorthParameterChart.northSet P :=
  NativeNorthSupportPatch.close_north P v₀ y (hy.trans (by norm_num))

def graphFar {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (graphSpace P) :=
  {z | 1 / 4 < ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ∨
    1 / 4 < ‖(z.2.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖}

theorem graphFar_open {n : ℕ} (P : Sphere n) (v₀ : equator P) : IsOpen (graphFar P v₀) := by
  have hl : Continuous (fun z : graphSpace P => ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖) := by fun_prop
  have hr : Continuous (fun z : graphSpace P => ‖(z.2.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖) := by fun_prop
  exact (isOpen_lt continuous_const hl).union (isOpen_lt continuous_const hr)

theorem graphFar_outside {n : ℕ} (P : Sphere n) (v₀ : equator P) : graphFar P v₀ ⊆ (graphGood P v₀)ᶜ := by
  intro z hz hg
  rcases hz with h | h
  · linarith [hg.1]
  · linarith [hg.2]

theorem graph_cover {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    interior (graphPatch P) ∪ interior (graphGood P v₀)ᶜ = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  by_cases h : ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 4 ∧
      ‖(z.2.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 4
  · left
    rw [(NativeNorthSupportPatch.graphPatch_open P).interior_eq]
    exact ⟨close_north P v₀ z.1 h.1, close_north P v₀ z.2.1 h.2⟩
  · right
    have hf : z ∈ graphFar P v₀ := by
      by_cases hl : ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 4
      · exact Or.inr (lt_of_not_ge (fun hr => h ⟨hl, hr⟩))
      · exact Or.inl (lt_of_not_ge hl)
    apply interior_mono (graphFar_outside P v₀)
    rw [(graphFar_open P v₀).interior_eq]
    exact hf

theorem native_cover {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    interior (nativePatch P) ∪ interior (NativeQuarterSupport.good P v₀)ᶜ = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hz := Set.eq_univ_iff_forall.mp (graph_cover P v₀) (sphereCoordinates P z)
  rcases hz with hz | hz
  · left
    exact ((sphereCoordinates P).hom.continuous.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hz))
      |> mem_interior_iff_mem_nhds.mpr
  · right
    change z ∈ interior (sphereCoordinates P ⁻¹' (graphGood P v₀)ᶜ)
    exact ((sphereCoordinates P).hom.continuous.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hz))
      |> mem_interior_iff_mem_nhds.mpr

abbrev patchHomeomorph {n : ℕ} (P : Sphere n) := NativeNorthSupportPatch.patchHomeomorph P

theorem maps_patch {n : ℕ} (P : Sphere n) : Set.MapsTo (sphereCoordinates P) (nativePatch P) (graphPatch P) := fun _ h => h
theorem maps_support {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (sphereCoordinates P) (NativeQuarterSupport.good P v₀)ᶜ (graphGood P v₀)ᶜ := fun _ h => h

theorem patchPair_isIso {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    IsIso (TopPair.interPairMap (sphereCoordinates P) (maps_patch P) (maps_support P v₀)) := by
  let F := TopPair.interPairMap (sphereCoordinates P) (maps_patch P) (maps_support P v₀)
  have he : TopPair.Hom.fst F = (TopCat.isoOfHomeo (patchHomeomorph P)).hom := by
    apply TopCat.ext
    intro z
    apply Subtype.ext
    exact TopPair.interPairMap_fst_apply (sphereCoordinates P) (maps_patch P) (maps_support P v₀) z
  have : IsIso (TopPair.Hom.fst F) := by rw [he]; infer_instance
  apply TopPair.isIso_of_isIso_fst_of_surjective_snd F
  intro y
  let x := (patchHomeomorph P).symm y.val
  have hx : sphereCoordinates P x.val = y.val.val := congrArg Subtype.val ((patchHomeomorph P).apply_symm_apply y.val)
  have hb : x.val ∈ (NativeQuarterSupport.good P v₀)ᶜ := by
    change sphereCoordinates P x.val ∈ (graphGood P v₀)ᶜ
    rw [hx]
    exact y.property
  refine ⟨⟨x, hb⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (TopPair.interPairMap_snd_apply (sphereCoordinates P) (maps_patch P) (maps_support P v₀) ⟨x, hb⟩).trans hx

end
end Finsler.NativeQuarterGraphPatch
