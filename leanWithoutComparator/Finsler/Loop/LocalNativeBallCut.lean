module

public import Finsler.Loop.SmallBallProductReduction
public import Finsler.Loop.NativeCutGraphDescent

/-! Extend the ORIGINAL native tested/retained cut maps to the WHOLE
product of two actual radius-one-third spherical balls and the
remaining equator. The real universal endpoint-distance<1 tube
contains this product. Restriction recovers the SAME original maps
at EVERY smaller actual radius<=1. A true product contraction reduces
their ordinary cohomology to the real Q,Q center slice. -/
@[expose] public section
namespace Finsler.LocalNativeBallCut
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates Finsler.SupportedCapNaturality
open Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

abbrev center {n : ℕ} (P : Sphere n) (v₀ : equator P) := NorthMeridianEvaluationPoint.target P v₀
abbrev space {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  SmallBallProductReduction.space (center P v₀) (TopCat.of (equator P))

def toGraph {n : ℕ} (P : Sphere n) (v₀ : equator P) : space P v₀ ⟶ graphSpace P :=
  TopCat.ofHom ⟨fun z => (z.1.val, (z.2.1.val, z.2.2)),
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd.fst).prodMk continuous_snd.snd)⟩

theorem toGraph_north {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : space P v₀) :
    toGraph P v₀ z ∈ NativeNorthSupportPatch.graphPatch P := by
  constructor
  · exact NativeNorthSupportPatch.close_north P v₀ z.1.val
      (z.1.property.le.trans (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2))
  · exact NativeNorthSupportPatch.close_north P v₀ z.2.1.val
      (z.2.1.property.le.trans (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2))

def toGraphPatch {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    space P v₀ ⟶ TopCat.of (NativeNorthSupportPatch.graphPatch P) :=
  TopCat.ofHom ⟨fun z => ⟨toGraph P v₀ z, toGraph_north P v₀ z⟩, (toGraph P v₀).hom.continuous.subtype_mk _⟩

def toNative {n : ℕ} (P : Sphere n) (v₀ : equator P) : space P v₀ ⟶ parameters P :=
  toGraphPatch P v₀ ≫ TopCat.ofHom ⟨NativeNorthSupportPatch.patchInverse P,
    NativeNorthSupportPatch.continuous_patchInverse P⟩ ≫
      SupportedCap.subspaceMap (parameters P) (NativeNorthSupportPatch.nativePatch P)

theorem coordinates {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    toNative P v₀ ≫ sphereCoordinates P = toGraph P v₀ := by
  apply TopCat.ext
  intro z
  exact congrArg Subtype.val (NativeNorthSupportPatch.patch_forward_inverse P (toGraphPatch P v₀ z))

def cutParameters {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    space P v₀ ⟶ SelfCutThomCocycle.parameters n := toNative P v₀ ≫ intoCut P v₀ b

theorem self_evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : space P v₀) :
    SelfCutThomCocycle.selfEvaluation n (cutParameters P v₀ b z) = (z.1.val, z.2.1.val) := by
  have he := selfEvaluation_value n P v₀ b (toNative P v₀ z)
  have hc := ConcreteCategory.congr_hom (coordinates P v₀) z
  have hl := congrArg (fun a : graphSpace P => a.1) hc
  have hr := congrArg (fun a : graphSpace P => a.2.1) hc
  exact he.trans (Prod.ext hl hr)

def toTube {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    space P v₀ ⟶ TopCat.of (H1SelfCutNeighborhood.tube n) :=
  TopCat.ofHom ⟨fun z => ⟨cutParameters P v₀ b z, by
    have he := self_evaluation P v₀ b z
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    change H1FiberBase.point (cutParameters P v₀ b z).2 = z.1.val at hl
    change H1SelfCutNeighborhood.endpoint (cutParameters P v₀ b z) = z.2.1.val at hr
    change ‖(H1SelfCutNeighborhood.endpoint (cutParameters P v₀ b z) : Ambient n) -
      (H1FiberBase.point (cutParameters P v₀ b z).2 : Ambient n)‖ < 1
    rw [hl, hr]
    exact SmallSphereBallContraction.pair_tube (center P v₀) z.1 z.2.1⟩,
    (cutParameters P v₀ b).hom.continuous.subtype_mk _⟩

def testedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : space P v₀ ⟶ TopCat.of (SphereLoop n) :=
  toTube P v₀ b ≫ TopCat.ofHom ⟨H1SelfCutNeighborhood.left, H1SelfCutNeighborhood.continuous_left⟩
def retainedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : space P v₀ ⟶ TopCat.of (SphereLoop n) :=
  toTube P v₀ b ≫ TopCat.ofHom ⟨H1SelfCutNeighborhood.right, H1SelfCutNeighborhood.continuous_right⟩

def near {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) : Set (space P v₀) :=
  {z | SupportedSelfCut.distance n (cutParameters P v₀ b z) < r}

def toNeighborhood {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) :
    TopCat.of (near P v₀ b r) ⟶ TopCat.of (SupportedSelfCut.neighborhood n r) :=
  TopCat.ofHom ⟨fun z => ⟨cutParameters P v₀ b z.val, z.property⟩,
    ((cutParameters P v₀ b).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem tested_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1) :
    SupportedCap.subspaceMap (space P v₀) (near P v₀ b r) ≫ testedH1 P v₀ b =
      toNeighborhood P v₀ b r ≫ TopCat.ofHom (SupportedSelfCut.tested n hr) := by
  apply TopCat.ext
  intro z
  rfl

theorem retained_restrict {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {r : ℝ} (hr : r ≤ 1) :
    SupportedCap.subspaceMap (space P v₀) (near P v₀ b r) ≫ retainedH1 P v₀ b =
      toNeighborhood P v₀ b r ≫ TopCat.ofHom (SupportedSelfCut.retained n hr) := by
  apply TopCat.ext
  intro z
  rfl

def tested {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : space P v₀ ⟶ ContinuousLoopModel.space n :=
  testedH1 P v₀ b ≫ ContinuousLoopModel.inclusion n
def retained {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : space P v₀ ⟶ ContinuousLoopModel.space n :=
  retainedH1 P v₀ b ≫ ContinuousLoopModel.inclusion n

def testedSlice {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    TopCat.of (equator P) ⟶ ContinuousLoopModel.space n :=
  SmallBallProductReduction.sectionMap (center P v₀) (TopCat.of (equator P)) ≫ tested P v₀ b
def retainedSlice {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    TopCat.of (equator P) ⟶ ContinuousLoopModel.space n :=
  SmallBallProductReduction.sectionMap (center P v₀) (TopCat.of (equator P)) ≫ retained P v₀ b

theorem tested_reduced {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (tested P v₀ b) q).hom a =
      (cohPullback (SmallBallProductReduction.remaining (center P v₀) (TopCat.of (equator P))) q).hom
        ((cohPullback (testedSlice P v₀ b) q).hom a) :=
  SmallBallProductReduction.pullback_reduced (center P v₀) (TopCat.of (equator P)) _ (tested P v₀ b) q a

theorem retained_reduced {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (retained P v₀ b) q).hom a =
      (cohPullback (SmallBallProductReduction.remaining (center P v₀) (TopCat.of (equator P))) q).hom
        ((cohPullback (retainedSlice P v₀ b) q).hom a) :=
  SmallBallProductReduction.pullback_reduced (center P v₀) (TopCat.of (equator P)) _ (retained P v₀ b) q a

end
end Finsler.LocalNativeBallCut
