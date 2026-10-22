module

public import Finsler.Loop.NativePairBoundaryRelativeCut
public import Finsler.Loop.NativePairPrimitiveLocalization

/-! Localize the ACTUAL relative native cut cochain to the region where
BOTH real meridian evaluation points are within1/2 of the chosen north
point. On this region BOTH direction maps avoid the fixed equator point,
so the ORIGINAL rotated source transgression is the remaining primitive.
Outside it the ORIGINAL full first-cap/split-cup cochain is literallyzero.
No native relative fundamental value or gluing formula is assumed. -/
@[expose] public section
namespace Finsler.NativePairGoodCarrier
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.NativeMeridianPairCoordinates Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def good {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (parameters P) :=
  {z | ‖(meridian P z.1.2 z.1.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 2 ∧
    ‖(meridian P z.2.1.2 z.2.1.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 2}

theorem good_first_ne {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : good P v₀) : z.val.1.2 ≠ v₀ := by
  intro h
  have ht := NorthMeridianEvaluationPoint.excluded_distance P v₀
    ⟨meridian P v₀ z.val.1.1, NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ _⟩
  have hz := z.property.1
  rw [h] at hz
  linarith

theorem good_second_ne {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : good P v₀) : z.val.2.1.2 ≠ v₀ := by
  intro h
  have ht := NorthMeridianEvaluationPoint.excluded_distance P v₀
    ⟨meridian P v₀ z.val.2.1.1, NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ _⟩
  have hz := z.property.2
  rw [h] at hz
  linarith

theorem outside_farCarrier (n : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (z : parameters P) (hz : z ∉ good P v₀) :
    intoCut P v₀ b z ∈ LocalizedParameterCutCochain.farCarrier n (NorthMeridianEvaluationPoint.target P v₀) (1 / 2) := by
  have he := selfEvaluation_value n P v₀ b z
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  change H1FiberBase.point (intoCut P v₀ b z).2 = meridian P z.1.2 z.1.1 at hl
  change H1SelfCutNeighborhood.endpoint (intoCut P v₀ b z) = meridian P z.2.1.2 z.2.1.1 at hr
  by_cases h : ‖(meridian P z.1.2 z.1.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 2
  · right
    rw [hr]
    exact le_of_not_gt (fun h₂ => hz ⟨h, h₂⟩)
  · left
    rw [hl]
    exact le_of_not_gt h

theorem bad_outside {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : parameters P) (hz : z ∈ NativePairBoundaryRelativeCut.bad P v₀) : z ∉ good P v₀ := by
  intro hg
  rcases NativePairBoundaryRelativeCut.bad_excluded P v₀ z hz with h | h
  · have ht := NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨meridian P z.1.2 z.1.1, h⟩
    linarith [hg.1]
  · have ht := NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨meridian P z.2.1.2 z.2.1.1, h⟩
    linarith [hg.2]

theorem original_source_primitive_reduced {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (q : ℕ) (hq : q ≠ 0) (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (SupportedCap.subspaceMap (parameters P) (good P v₀) ≫
      NativePairPrimitiveLocalization.shifted P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
    (cohPullback (SupportedCap.subspaceMap (parameters P) (good P v₀) ≫
      (NativePairPrimitiveLocalization.remainingDirection P ≫ ordinary P v₀)) q).hom (ContinuousLoopSweep.transgression n q a) :=
  NativePairPrimitiveLocalization.shifted_reduced P v₀ b _
    (good_first_ne P v₀) (good_second_ne P v₀) q hq a

theorem outside_cochain_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    cochainPullback (SupportedCap.subspaceMap (parameters P) (good P v₀)ᶜ) ((m + 1) + (p + (m + 1)))
      (NativePairBoundaryRelativeCut.cochain m p P v₀ b hρ hρr hr hη T) = 0 := by
  let i := SupportedCap.subspaceMap (parameters P) (good P v₀)ᶜ
  have hz := LocalizedParameterCutCochain.family_zero m p (NorthMeridianEvaluationPoint.target P v₀)
    hρ hρr hr hη (show η + r ≤ (1 / 2 : ℝ) by linarith) T (i ≫ intoCut P v₀ b)
    (fun x => outside_farCarrier (m + 1) P v₀ b x.val x.property)
  change cochainPullback i _ (cochainPullback (intoCut P v₀ b) _ _) = 0
  rw [← pullback_comp]
  exact hz

abbrev supportPair {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopPair.{0} :=
  TopPair.ofSubset (X := parameters P) (good P v₀)ᶜ

def boundaryToSupport {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativePairBoundaryRelativeCut.pair P v₀ ⟶ supportPair P v₀ :=
  TopPair.ofSubsetMap (B := NativePairBoundaryRelativeCut.bad P v₀) (B' := (good P v₀)ᶜ)
    (𝟙 (parameters P)) (fun z hz => bad_outside P v₀ z hz)

def relativeCocycle (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.relative (supportPair P v₀) ((m + 1) + (p + (m + 1))) :=
  (RelativeCupCochain.exists_lift (supportPair P v₀) _
    (NativePairBoundaryRelativeCut.cochain m p P v₀ b hρ hρr hr hη T)
    (outside_cochain_zero m p P v₀ b hρ hρr hr hη hr4 hη4 T)).choose

theorem relative_toAmbient (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.toAmbient (supportPair P v₀) _ (relativeCocycle m p P v₀ b hρ hρr hr hη hr4 hη4 T) =
      NativePairBoundaryRelativeCut.cochain m p P v₀ b hρ hρr hr hη T :=
  (RelativeCupCochain.exists_lift (supportPair P v₀) _
    (NativePairBoundaryRelativeCut.cochain m p P v₀ b hρ hρr hr hη T)
    (outside_cochain_zero m p P v₀ b hρ hρr hr hη hr4 hη4 T)).choose_spec

theorem relative_closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    RelativeCupCochain.differential (supportPair P v₀) ((m + 1) + (p + (m + 1)))
      (relativeCocycle m p P v₀ b hρ hρr hr hη hr4 hη4 T) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (supportPair P v₀) _
  rw [RelativeCupCochain.toAmbient_differential, relative_toAmbient, map_zero]
  exact NativePairBoundaryRelativeCut.closed m p P v₀ b hρ hρr hr hη T hT

def originalPrimitiveSupportClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    (supportPair P v₀).singularCohomology coeff (ZMod 2) coeff ((m + 1) + (m + (m + 1))) :=
  CochainClass.classOf (RelativeCup.cx (supportPair P v₀)) _
    (relativeCocycle m m P v₀ b hρ hρr hr hη hr4 hη4 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))
    (relative_closed m m P v₀ b hρ hρr hr hη hr4 hη4 _ (classRepr_isCocycle _ m _))


theorem boundaryToSupport_fst {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Hom.fst (boundaryToSupport P v₀) = 𝟙 (parameters P) := by
  ext z : 1
  exact TopPair.ofSubsetMap_fst_apply (B := NativePairBoundaryRelativeCut.bad P v₀)
    (B' := (good P v₀)ᶜ) (𝟙 (parameters P)) (fun x hx => bad_outside P v₀ x hx) z

private theorem cochain_id (X : TopCat.{0}) (N : ℕ) (φ : singularCochainGroup (ZMod 2) X N) :
    cochainPullback (𝟙 X) N φ = φ :=
  congrArg (fun f => (f.f N).hom φ) (singularCochainComplexZMod2.map_id (Opposite.op X))

theorem relative_boundary_pullback (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.pullback (boundaryToSupport P v₀) _
      (relativeCocycle m p P v₀ b hρ hρr hr hη hr4 hη4 T) =
        NativePairBoundaryRelativeCut.relativeCocycle m p P v₀ b hρ hρr hr hη hr4 hη4 T := by
  apply RelativeCupCochain.toAmbient_injective (NativePairBoundaryRelativeCut.pair P v₀) _
  rw [RelativeCupCochain.toAmbient_pullback, relative_toAmbient,
    NativePairBoundaryRelativeCut.relative_toAmbient, boundaryToSupport_fst]
  exact cochain_id (parameters P) _ _

theorem originalPrimitiveSupportClass_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (boundaryToSupport P v₀) ((m + 1) + (m + (m + 1)))).hom
        (originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr4 hη4) =
          NativePairBoundaryRelativeCut.originalPrimitiveClass m P v₀ b hρ hρr hr hη hr4 hη4 := by
  let N := (m + 1) + (m + (m + 1))
  let T := classRepr (Loops (m + 1)) m (MeridianLoopClass.H1TransgressionClass m)
  let f := TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (boundaryToSupport P v₀)
  let R := relativeCocycle m m P v₀ b hρ hρr hr hη hr4 hη4 T
  have hR := relative_closed m m P v₀ b hρ hρr hr hη hr4 hη4 T (classRepr_isCocycle _ m _)
  have hM := CochainClass.closed_map (RelativeCup.cx (supportPair P v₀)) f N R hR
  have he := CochainClass.classOf_map (RelativeCup.cx (supportPair P v₀)) f N R hR hM
  exact he.trans (CochainClass.classOf_congr (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) N
    (relative_boundary_pullback m m P v₀ b hρ hρr hr hη hr4 hη4 T) _ _)

end
end Finsler.NativePairGoodCarrier
