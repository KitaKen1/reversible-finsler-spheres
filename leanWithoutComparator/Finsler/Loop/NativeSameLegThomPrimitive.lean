module

public import Finsler.Loop.NativeSameLegCommonMaps
public import Finsler.Loop.SelfCutDistanceCoordinates

/-! Pull the SINGLE corrected common primitive back to both ACTUAL
same-leg inputs. Its boundary is the SAME original normalized Thom
cochain. It vanishes on every real exterior family and on the actual
short-time-zero or long-time-one seam family. No union-zero or full
cap scalar vanishing is assumed. -/
@[expose] public section
namespace Finsler.NativeSameLegThomPrimitive
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelEvaluation Finsler.NativeMovingNonnorthGeometry Finsler.SameMeridianTransverseEscape
open Finsler.NativeSameLegCommonMaps Finsler.CommonMeridianThomPrimitive Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def cutIndex (isLong : Bool) : Fin 13 := if isLong then 12 else 0

def input {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) :
    localSpace P v₀ k ⟶ base P (NorthMeridianEvaluationPoint.opposite v₀) :=
  if isLong then longMap P v₀ k else shortMap P v₀ k

def family {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) :
    localSpace P v₀ k ⟶ SelfCutThomCocycle.parameters n :=
  SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k (cutIndex isLong)

theorem input_pair {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) :
    input P v₀ k isLong ≫ OrthogonalSphereEscape.pair (firstPoint P (NorthMeridianEvaluationPoint.opposite v₀))
      (secondPoint P (NorthMeridianEvaluationPoint.opposite v₀)) = family P v₀ k isLong ≫ SelfCutThomCocycle.selfEvaluation n := by
  cases isLong
  · exact NativeSameLegCommonMaps.short_pair P v₀ k
  · exact NativeSameLegCommonMaps.long_pair P v₀ k

def primitive {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : singularCochainGroup (ZMod 2) (localSpace P v₀ k) (n - 1) :=
  cochainPullback (input P v₀ k isLong) (n - 1)
    (CommonMeridianThomSeamCorrection.corrected hn P (NorthMeridianEvaluationPoint.opposite v₀) hρ hρ1)

theorem primitive_d {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((cochainCxZMod2 (localSpace P v₀ k)).d (n - 1) n).hom (primitive hn P v₀ k isLong hρ hρ1) =
      cochainPullback (family P v₀ k isLong) n (NormalizedSelfCut.cocycle n (by omega) hρ) := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (input P v₀ k isLong).op).comm (n - 1) n)
    (CommonMeridianThomSeamCorrection.corrected hn P (NorthMeridianEvaluationPoint.opposite v₀) hρ hρ1)
  change ((cochainCxZMod2 (localSpace P v₀ k)).d (n - 1) n).hom (primitive hn P v₀ k isLong hρ hρ1) =
    cochainPullback (input P v₀ k isLong) n
      (((cochainCxZMod2 (base P (NorthMeridianEvaluationPoint.opposite v₀))).d (n - 1) n).hom
        (CommonMeridianThomSeamCorrection.corrected hn P (NorthMeridianEvaluationPoint.opposite v₀) hρ hρ1)) at he
  rw [CommonMeridianThomSeamCorrection.corrected_d, ← pullback_comp, input_pair] at he
  exact he.trans (pullback_comp (family P v₀ k isLong) (SelfCutThomCocycle.selfEvaluation n) n _)

theorem distance_model {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (z : localSpace P v₀ k) :
    ‖(secondPoint P (NorthMeridianEvaluationPoint.opposite v₀) (input P v₀ k isLong z) : Ambient n) -
      (firstPoint P (NorthMeridianEvaluationPoint.opposite v₀) (input P v₀ k isLong z) : Ambient n)‖ =
      SupportedSelfCut.distance n (family P v₀ k isLong z) :=
  SelfCutDistanceCoordinates.map_distance (firstPoint P (NorthMeridianEvaluationPoint.opposite v₀))
    (secondPoint P (NorthMeridianEvaluationPoint.opposite v₀))
    (input P v₀ k isLong) (family P v₀ k isLong) (input_pair P v₀ k isLong) z

theorem primitive_far_family_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Y : TopCat.{0}} (f : Y ⟶ localSpace P v₀ k)
    (hf : ∀ y, ρ ≤ SupportedSelfCut.distance n (family P v₀ k isLong (f y))) :
    cochainPullback f (n - 1) (primitive hn P v₀ k isLong hρ hρ1) = 0 := by
  let V := NorthMeridianEvaluationPoint.opposite v₀
  let A := OrthogonalRelativeThomZero.exterior (firstPoint P V) (secondPoint P V) (ρ := ρ)
  have hm (y : Y) : input P v₀ k isLong (f y) ∈ A := by
    change ρ ≤ ‖(secondPoint P V (input P v₀ k isLong (f y)) : Ambient n) -
      (firstPoint P V (input P v₀ k isLong (f y)) : Ambient n)‖
    rw [distance_model]
    exact hf y
  let g : Y ⟶ TopCat.of A := TopCat.ofHom ⟨fun y => ⟨input P v₀ k isLong (f y), hm y⟩,
    ((input P v₀ k isLong).hom.continuous.comp f.hom.continuous).subtype_mk _⟩
  have he : f ≫ input P v₀ k isLong = g ≫ (pair P V ρ).map := by
    apply TopCat.ext
    intro y
    rfl
  rw [primitive, ← pullback_comp, he, pullback_comp, CommonMeridianThomSeamCorrection.corrected_far_zero]
  exact map_zero _

def seam {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) : Set (localSpace P v₀ k) :=
  {z | z.val.2.down = if isLong then 1 else 0}

theorem input_seam {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (z : localSpace P v₀ k)
    (hz : z ∈ seam P v₀ k isLong) :
    input P v₀ k isLong z ∈ CommonMeridianThomSeamCorrection.diagonalSet P (NorthMeridianEvaluationPoint.opposite v₀) := by
  cases isLong
  · exact NativeSameLegCommonMaps.short_seam P v₀ k z hz
  · exact NativeSameLegCommonMaps.long_seam P v₀ k z hz

theorem primitive_seam_family_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Y : TopCat.{0}} (f : Y ⟶ localSpace P v₀ k)
    (hf : ∀ y, f y ∈ seam P v₀ k isLong) :
    cochainPullback f (n - 1) (primitive hn P v₀ k isLong hρ hρ1) = 0 := by
  let V := NorthMeridianEvaluationPoint.opposite v₀
  let g : Y ⟶ diagonal P V := TopCat.ofHom ⟨fun y =>
    ((input P v₀ k isLong (f y)).1.1, (input P v₀ k isLong (f y)).2), by
      exact ((continuous_fst.comp (continuous_fst.comp ((input P v₀ k isLong).hom.continuous.comp f.hom.continuous))).prodMk
        (continuous_snd.comp ((input P v₀ k isLong).hom.continuous.comp f.hom.continuous)))⟩
  have he : f ≫ input P v₀ k isLong = g ≫ diagonalMap P V := by
    apply TopCat.ext
    intro y
    have hy := input_seam P v₀ k isLong (f y) (hf y)
    exact Prod.ext (Prod.ext rfl hy.symm) rfl
  rw [primitive, ← pullback_comp, he, pullback_comp, CommonMeridianThomSeamCorrection.corrected_diagonal_zero]
  exact map_zero _

end
end Finsler.NativeSameLegThomPrimitive
