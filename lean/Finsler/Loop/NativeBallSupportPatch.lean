module

public import Finsler.Loop.LocalNativeBallCut
public import Finsler.Loop.NativeQuarterGraphPatch

/-! The genuine quarter support lies inside the two radius1/3 balls.
The ACTUAL ball-product inclusion is an isomorphism on the excision
patch, hence its real supported cohomology pullback is invertible. -/
@[expose] public section
namespace Finsler.NativeBallSupportPatch
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates
open Finsler.NativePairRelativeSphereTransport Finsler.LocalNativeBallCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def graphBall {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (graphSpace P) :=
  {z | z.1 ∈ SmallSphereBallContraction.ball (center P v₀) ∧
    z.2.1 ∈ SmallSphereBallContraction.ball (center P v₀)}

theorem graphBall_open {n : ℕ} (P : Sphere n) (v₀ : equator P) : IsOpen (graphBall P v₀) :=
  ((SmallSphereBallContraction.ball_open (center P v₀)).preimage continuous_fst).inter
    ((SmallSphereBallContraction.ball_open (center P v₀)).preimage continuous_snd.fst)

theorem graph_cover {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    interior (graphBall P v₀) ∪ interior (NativeQuarterGraphPatch.graphGood P v₀)ᶜ = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  by_cases h : ‖(z.1 : Ambient n) - (center P v₀ : Ambient n)‖ ≤ 1 / 4 ∧
      ‖(z.2.1 : Ambient n) - (center P v₀ : Ambient n)‖ ≤ 1 / 4
  · left
    rw [(graphBall_open P v₀).interior_eq]
    exact ⟨SmallSphereBallContraction.quarter_inside _ _ h.1,
      SmallSphereBallContraction.quarter_inside _ _ h.2⟩
  · right
    have hf : z ∈ NativeQuarterGraphPatch.graphFar P v₀ := by
      by_cases hl : ‖(z.1 : Ambient n) - (center P v₀ : Ambient n)‖ ≤ 1 / 4
      · exact Or.inr (lt_of_not_ge (fun hr => h ⟨hl, hr⟩))
      · exact Or.inl (lt_of_not_ge hl)
    apply interior_mono (NativeQuarterGraphPatch.graphFar_outside P v₀)
    rw [(NativeQuarterGraphPatch.graphFar_open P v₀).interior_eq]
    exact hf

def localGood {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (space P v₀) :=
  toGraph P v₀ ⁻¹' NativeQuarterGraphPatch.graphGood P v₀

abbrev localPair {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopPair.{0} :=
  TopPair.ofSubset (X := space P v₀) (localGood P v₀)ᶜ
abbrev graphPair {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopPair.{0} :=
  TopPair.ofSubset (X := graphSpace P) (NativeQuarterGraphPatch.graphGood P v₀)ᶜ

theorem maps_patch {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (toGraph P v₀) Set.univ (graphBall P v₀) := fun z _ => ⟨z.1.property, z.2.1.property⟩
theorem maps_support {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    Set.MapsTo (toGraph P v₀) (localGood P v₀)ᶜ (NativeQuarterGraphPatch.graphGood P v₀)ᶜ := fun _ h => h

def patchHomeomorph {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    (Set.univ : Set (space P v₀)) ≃ₜ graphBall P v₀ where
  toFun z := ⟨toGraph P v₀ z.val, ⟨z.val.1.property, z.val.2.1.property⟩⟩
  invFun y := ⟨(⟨y.val.1, y.property.1⟩, (⟨y.val.2.1, y.property.2⟩, y.val.2.2)), Set.mem_univ _⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl
  continuous_toFun := ((toGraph P v₀).hom.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hl : Continuous (fun y : graphBall P v₀ =>
      (⟨y.val.1, y.property.1⟩ : SmallSphereBallContraction.space (center P v₀))) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have hr : Continuous (fun y : graphBall P v₀ =>
      (⟨y.val.2.1, y.property.2⟩ : SmallSphereBallContraction.space (center P v₀))) :=
      (continuous_snd.fst.comp continuous_subtype_val).subtype_mk _
    exact (hl.prodMk (hr.prodMk (continuous_snd.snd.comp continuous_subtype_val))).subtype_mk _

theorem patchPair_isIso {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    IsIso (TopPair.interPairMap (toGraph P v₀) (maps_patch P v₀) (maps_support P v₀)) := by
  let F := TopPair.interPairMap (toGraph P v₀) (maps_patch P v₀) (maps_support P v₀)
  have he : TopPair.Hom.fst F = (TopCat.isoOfHomeo (patchHomeomorph P v₀)).hom := by
    apply TopCat.ext
    intro z
    apply Subtype.ext
    exact TopPair.interPairMap_fst_apply (toGraph P v₀) (maps_patch P v₀) (maps_support P v₀) z
  have : IsIso (TopPair.Hom.fst F) := by rw [he]; infer_instance
  apply TopPair.isIso_of_isIso_fst_of_surjective_snd F
  intro y
  let x := (patchHomeomorph P v₀).symm y.val
  have hx : toGraph P v₀ x.val = y.val.val :=
    congrArg Subtype.val ((patchHomeomorph P v₀).apply_symm_apply y.val)
  have hb : x.val ∈ (localGood P v₀)ᶜ := by
    change toGraph P v₀ x.val ∈ (NativeQuarterGraphPatch.graphGood P v₀)ᶜ
    rw [hx]
    exact y.property
  refine ⟨⟨x, hb⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (TopPair.interPairMap_snd_apply (toGraph P v₀) (maps_patch P v₀) (maps_support P v₀) ⟨x, hb⟩).trans hx

def inclusion {n : ℕ} (P : Sphere n) (v₀ : equator P) : localPair P v₀ ⟶ graphPair P v₀ :=
  TopPair.ofSubsetMap (toGraph P v₀) (maps_support P v₀)

theorem homology_isIso {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    IsIso (TopPair.singularHomologyMap (inclusion P v₀) coeff q) := by
  have := patchPair_isIso P v₀
  exact RelativeSupportPatchExcision.homology_isIso (toGraph P v₀) (maps_patch P v₀) (maps_support P v₀)
    (by simp) (graph_cover P v₀) q

def cohomologyEquiv {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    RelativeCup.cohomology (graphPair P v₀) q ≃ₗ[ZMod 2] RelativeCup.cohomology (localPair P v₀) q := by
  have := homology_isIso P v₀ q
  exact RelativeHomologyIsoCohomology.equiv (inclusion P v₀) q

theorem cohomologyEquiv_apply {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : RelativeCup.cohomology (graphPair P v₀) q) :
    cohomologyEquiv P v₀ q a =
      (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (inclusion P v₀) q).hom a := by
  have := homology_isIso P v₀ q
  exact RelativeHomologyIsoCohomology.equiv_apply (inclusion P v₀) q a

end
end Finsler.NativeBallSupportPatch
