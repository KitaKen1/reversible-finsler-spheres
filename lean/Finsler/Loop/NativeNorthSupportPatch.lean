module

public import Finsler.Loop.MeridianNorthParameterChart
public import Finsler.Loop.NativeDoubleFundamentalImage
public import Finsler.Loop.NativePairGoodCarrier
public import Finsler.Loop.RelativeSupportPatchExcision

/-! The ACTUAL two-meridian map is a homeomorphism on the genuine
north-minus-poles patch. Both original support complements admit
real excision covers, and the actual patch pair map is an isomorphism.
The support cohomology descent can therefore use actual invertible maps. -/
@[expose] public section
namespace Finsler.NativeNorthSupportPatch
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
  {z | ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 2 ∧
    ‖(z.2.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 2}

def graphPatch {n : ℕ} (P : Sphere n) : Set (graphSpace P) :=
  {z | z.1 ∈ MeridianNorthParameterChart.northSet P ∧ z.2.1 ∈ MeridianNorthParameterChart.northSet P}
def nativePatch {n : ℕ} (P : Sphere n) : Set (parameters P) := sphereCoordinates P ⁻¹' graphPatch P

theorem good_preimage {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    sphereCoordinates P ⁻¹' graphGood P v₀ = NativePairGoodCarrier.good P v₀ := rfl

theorem graphPatch_open {n : ℕ} (P : Sphere n) : IsOpen (graphPatch P) :=
  ((RationalNorthMeridianChart.north_isOpen P).preimage continuous_fst).inter
    ((RationalNorthMeridianChart.north_isOpen P).preimage continuous_snd.fst)

theorem close_north {n : ℕ} (P : Sphere n) (v₀ : equator P) (y : Sphere n)
    (hy : ‖(y : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 2) :
    y ∈ MeridianNorthParameterChart.northSet P := by
  constructor
  · by_contra h
    have hd := NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨y, Or.inr (le_of_not_gt h)⟩
    linarith
  · intro h
    have hp : P ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
      simpa only [Path.source] using NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ 0
    have hd := NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨P, hp⟩
    rw [h] at hy
    linarith

def graphFar {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (graphSpace P) :=
  {z | 1 / 2 < ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ∨
    1 / 2 < ‖(z.2.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖}

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
  by_cases h : ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 2 ∧
      ‖(z.2.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 2
  · left
    rw [(graphPatch_open P).interior_eq]
    exact ⟨close_north P v₀ z.1 h.1, close_north P v₀ z.2.1 h.2⟩
  · right
    have hf : z ∈ graphFar P v₀ := by
      by_cases hl : ‖(z.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ ≤ 1 / 2
      · exact Or.inr (lt_of_not_ge (fun hr => h ⟨hl, hr⟩))
      · exact Or.inl (lt_of_not_ge hl)
    apply interior_mono (graphFar_outside P v₀)
    rw [(graphFar_open P v₀).interior_eq]
    exact hf

theorem native_cover {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    interior (nativePatch P) ∪ interior (NativePairGoodCarrier.good P v₀)ᶜ = Set.univ := by
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

def patchForward {n : ℕ} (P : Sphere n) (z : nativePatch P) : graphPatch P :=
  ⟨sphereCoordinates P z.val, z.property⟩

def patchInverse {n : ℕ} (P : Sphere n) (y : graphPatch P) : nativePatch P :=
  ⟨((MeridianNorthParameterChart.inverse P ⟨y.val.1, y.property.1⟩).val,
    ((MeridianNorthParameterChart.inverse P ⟨y.val.2.1, y.property.2⟩).val, y.val.2.2)),
    (MeridianNorthParameterChart.inverse P ⟨y.val.1, y.property.1⟩).property,
    (MeridianNorthParameterChart.inverse P ⟨y.val.2.1, y.property.2⟩).property⟩

theorem patch_inverse_forward {n : ℕ} (P : Sphere n) (z : nativePatch P) : patchInverse P (patchForward P z) = z := by
  have hl := congrArg Subtype.val (MeridianNorthParameterChart.inverse_forward P ⟨z.val.1, z.property.1⟩)
  have hr := congrArg Subtype.val (MeridianNorthParameterChart.inverse_forward P ⟨z.val.2.1, z.property.2⟩)
  apply Subtype.ext
  exact Prod.ext hl (Prod.ext hr rfl)

theorem patch_forward_inverse {n : ℕ} (P : Sphere n) (y : graphPatch P) : patchForward P (patchInverse P y) = y := by
  have hl := congrArg Subtype.val (MeridianNorthParameterChart.forward_inverse P ⟨y.val.1, y.property.1⟩)
  have hr := congrArg Subtype.val (MeridianNorthParameterChart.forward_inverse P ⟨y.val.2.1, y.property.2⟩)
  apply Subtype.ext
  exact Prod.ext hl (Prod.ext hr rfl)

theorem continuous_patchForward {n : ℕ} (P : Sphere n) : Continuous (patchForward P) :=
  ((sphereCoordinates P).hom.continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_patchInverse {n : ℕ} (P : Sphere n) : Continuous (patchInverse P) := by
  have hl : Continuous (fun y : graphPatch P => (⟨y.val.1, y.property.1⟩ : RationalNorthMeridianChart.north P)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hr : Continuous (fun y : graphPatch P => (⟨y.val.2.1, y.property.2⟩ : RationalNorthMeridianChart.north P)) :=
    (continuous_snd.fst.comp continuous_subtype_val).subtype_mk _
  have hli := (MeridianNorthParameterChart.continuous_inverse P).comp hl
  have hri := (MeridianNorthParameterChart.continuous_inverse P).comp hr
  exact ((continuous_subtype_val.comp hli).prodMk ((continuous_subtype_val.comp hri).prodMk
    (continuous_snd.snd.comp continuous_subtype_val))).subtype_mk _

def patchHomeomorph {n : ℕ} (P : Sphere n) : nativePatch P ≃ₜ graphPatch P where
  toFun := patchForward P
  invFun := patchInverse P
  left_inv := patch_inverse_forward P
  right_inv := patch_forward_inverse P
  continuous_toFun := continuous_patchForward P
  continuous_invFun := continuous_patchInverse P

theorem maps_patch {n : ℕ} (P : Sphere n) : Set.MapsTo (sphereCoordinates P) (nativePatch P) (graphPatch P) := fun _ h => h
theorem maps_support {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (sphereCoordinates P) (NativePairGoodCarrier.good P v₀)ᶜ (graphGood P v₀)ᶜ := fun _ h => h

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
  have hb : x.val ∈ (NativePairGoodCarrier.good P v₀)ᶜ := by
    change sphereCoordinates P x.val ∈ (graphGood P v₀)ᶜ
    rw [hx]
    exact y.property
  refine ⟨⟨x, hb⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (TopPair.interPairMap_snd_apply (sphereCoordinates P) (maps_patch P) (maps_support P v₀) ⟨x, hb⟩).trans hx

end
end Finsler.NativeNorthSupportPatch
