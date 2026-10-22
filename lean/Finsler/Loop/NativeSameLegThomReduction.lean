module

public import Finsler.Loop.SameMeridianTransverseEscape
public import Finsler.Loop.OrthogonalThomPrimitive

/-! Apply the excess-direction escape to the ACTUAL two same-leg
families. The pulled cocycles are literally those of the ORIGINAL
normalized first Thom cap. Their far-relative classes vanish and
have genuine far-relative primitives. The old full cap is zero
outside the real local direction patch. Diagonal/time-seam corrections
for the eventual full cap are still a separate obligation. -/
@[expose] public section
namespace Finsler.NativeSameLegThomReduction
open CategoryTheory MonoidalCategory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.SameMeridianTransverseEscape Finsler.NativeMovingNonnorthGeometry
open Finsler.MeridianTripleQuarterClocks Finsler.RationalSphereArc Finsler.RationalSphereArcCoordinates
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem original_start {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (j : Fin 13) (z : domain P) :
    H1FiberBase.point (segmentFamily P v₀ k j z).2 =
      piece P v₀ (NativeTripleSelfEvaluation.directions z.1.2 k) 0 z.1.1 := by
  change H1FiberBase.point (SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀ z.1.2)
    (clock k 0 z.1.1)) = _
  rw [NativeTripleSelfEvaluation.point_shift, NativeTripleSelfEvaluation.circle_quarter]

theorem outside_start_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (j : Fin 13)
    (z : domain P) (hz : z ∉ localSet P v₀ k) :
    H1FiberBase.point (segmentFamily P v₀ k j z).2 ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  rw [original_start]
  apply Or.inl
  have hv : 0 ≤ ⟪(v₀.val : Ambient n), ((NativeTripleSelfEvaluation.directions z.1.2 k).val : Ambient n)⟫ := by
    change ¬ 0 < ⟪((NativeTripleSelfEvaluation.directions z.1.2 k).val : Ambient n), -(v₀.val : Ambient n)⟫ at hz
    rw [inner_neg_right, real_inner_comm] at hz
    linarith
  have hP : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
  change ⟪(v₀.val : Ambient n), (point (outgoing P _) z.1.1 : Ambient n)⟫ ≥ 0
  rw [coordinates, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  change alpha z.1.1 * ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ +
    beta z.1.1 * ⟪(v₀.val : Ambient n), ((NativeTripleSelfEvaluation.directions z.1.2 k).val : Ambient n)⟫ ≥ 0
  rw [hP, mul_zero, zero_add]
  exact mul_nonneg (beta_nonneg z.1.1) hv

theorem outside_original_cap_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (j : Fin 13)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    cochainPullback (SupportedCap.subspaceMap (domain P) (localSet P v₀ k)ᶜ ≫ segmentFamily P v₀ k j)
      ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) = 0 :=
  NativeGlobalSquareFaceZero.parameter_start_family_zero m p P v₀ hρ hρr hr hη hη2 T _
    (fun z => outside_start_excluded P v₀ k j z.val z.property)

theorem short_map {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    OrthogonalSphereEscape.pair (first P v₀ k) (shortEnd P v₀ k) =
      SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 0 ≫ SelfCutThomCocycle.selfEvaluation n := by
  apply TopCat.ext
  intro z
  rfl

theorem long_map {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) :
    OrthogonalSphereEscape.pair (first P v₀ k) (longEnd P v₀ k) =
      SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 12 ≫ SelfCutThomCocycle.selfEvaluation n := by
  apply TopCat.ext
  intro z
  rfl

theorem coordinate_fst {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) (ρ : ℝ) :
    TopPair.Hom.fst (OrthogonalRelativeThomZero.pairMap f g (ρ := ρ)) = OrthogonalSphereEscape.pair f g := by
  apply TopCat.ext
  intro x
  exact TopPair.ofSubsetMap_fst_apply (B := OrthogonalRelativeThomZero.exterior f g (ρ := ρ))
    (B' := DiagonalAvoidanceCocycle.far n ρ) (OrthogonalSphereEscape.pair f g) (fun _ hx => hx) x

theorem short_cochain_original {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (OrthogonalRelativeThomZero.source (first P v₀ k) (shortEnd P v₀ k) (ρ := ρ)) n
      (OrthogonalThomPrimitive.cocycle (first P v₀ k) (shortEnd P v₀ k) hρ (by omega)) =
      cochainPullback (SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 0) n
        (NormalizedSelfCut.cocycle n (by omega) hρ) := by
  rw [OrthogonalThomPrimitive.cocycle, RelativeCupCochain.toAmbient_pullback,
    NormalizedDiagonalCocycle.relative_toAmbient, coordinate_fst, short_map,
    NormalizedSelfCut.cocycle]
  simp only [pullback_comp]

theorem long_cochain_original {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (OrthogonalRelativeThomZero.source (first P v₀ k) (longEnd P v₀ k) (ρ := ρ)) n
      (OrthogonalThomPrimitive.cocycle (first P v₀ k) (longEnd P v₀ k) hρ (by omega)) =
      cochainPullback (SupportedCap.subspaceMap (domain P) (localSet P v₀ k) ≫ segmentFamily P v₀ k 12) n
        (NormalizedSelfCut.cocycle n (by omega) hρ) := by
  rw [OrthogonalThomPrimitive.cocycle, RelativeCupCochain.toAmbient_pullback,
    NormalizedDiagonalCocycle.relative_toAmbient, coordinate_fst, long_map,
    NormalizedSelfCut.cocycle]
  simp only [pullback_comp]

theorem short_class_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    CochainClass.classOf (RelativeCup.cx (OrthogonalRelativeThomZero.source (first P v₀ k) (shortEnd P v₀ k) (ρ := ρ))) n
      (OrthogonalThomPrimitive.cocycle (first P v₀ k) (shortEnd P v₀ k) hρ (by omega))
      (OrthogonalThomPrimitive.cocycle_closed (first P v₀ k) (shortEnd P v₀ k) hρ (by omega)) = 0 :=
  OrthogonalThomPrimitive.class_zero (first P v₀ k) (shortEnd P v₀ k) (normal hn P v₀ k)
    (short_perp hn P v₀ k) (first_perp hn P v₀ k) hρ hρ1 (by omega)

theorem long_class_zero {n : ℕ} (hn : 2 ≤ n) (P : Sphere n) (v₀ : equator P) (k : Fin 3)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    CochainClass.classOf (RelativeCup.cx (OrthogonalRelativeThomZero.source (first P v₀ k) (longEnd P v₀ k) (ρ := ρ))) n
      (OrthogonalThomPrimitive.cocycle (first P v₀ k) (longEnd P v₀ k) hρ (by omega))
      (OrthogonalThomPrimitive.cocycle_closed (first P v₀ k) (longEnd P v₀ k) hρ (by omega)) = 0 :=
  OrthogonalThomPrimitive.class_zero (first P v₀ k) (longEnd P v₀ k) (normal hn P v₀ k)
    (long_perp hn P v₀ k) (first_perp hn P v₀ k) hρ hρ1 (by omega)

end
end Finsler.NativeSameLegThomReduction
