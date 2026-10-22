module

public import Finsler.Loop.NativeMeridianPairCoordinates
public import Finsler.Loop.LocalizedParameterCutCochain
public import Finsler.Loop.NorthMeridianEvaluationPoint

/-! The ORIGINAL native first-Thom-plus-tested/evaluation cochain
vanishes LITERALLY on all FOUR time faces and both fixed-direction
faces. It therefore defines a genuine RELATIVE cohomology class in
the required total degree. The source is not falsely treated as an
absolute cycle; its relative fundamental pairing is still to compute. -/
@[expose] public section
namespace Finsler.NativePairBoundaryRelativeCut
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.NativeMeridianPairCoordinates Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def bad {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (parameters P) :=
  {z | z.1.1 = 0 ∨ z.1.1 = 1 ∨ z.2.1.1 = 0 ∨ z.2.1.1 = 1 ∨ z.1.2 = v₀ ∨ z.2.1.2 = v₀}

theorem bad_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P) (hz : z ∈ bad P v₀) :
    meridian P z.1.2 z.1.1 ∈ NorthMeridianEvaluationPoint.excluded P v₀ ∨
      meridian P z.2.1.2 z.2.1.1 ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  rcases hz with h | h | h | h | h | h
  · left
    simpa only [h, Path.source] using NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ 0
  · left
    simpa only [h, Path.target] using NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ 1
  · right
    simpa only [h, Path.source] using NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ 0
  · right
    simpa only [h, Path.target] using NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ 1
  · left
    rw [h]
    exact NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ _
  · right
    rw [h]
    exact NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ _

theorem bad_farCarrier (n : ℕ) (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (z : parameters P) (hz : z ∈ bad P v₀) :
    intoCut P v₀ b z ∈ LocalizedParameterCutCochain.farCarrier n (NorthMeridianEvaluationPoint.target P v₀) (3 / 5) := by
  have he := selfEvaluation_value n P v₀ b z
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  change H1FiberBase.point (intoCut P v₀ b z).2 = meridian P z.1.2 z.1.1 at hl
  change H1SelfCutNeighborhood.endpoint (intoCut P v₀ b z) = meridian P z.2.1.2 z.2.1.1 at hr
  rcases bad_excluded P v₀ z hz with h | h
  · left
    rw [hl]
    exact NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨_, h⟩
  · right
    rw [hr]
    exact NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨_, h⟩

abbrev pair {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopPair.{0} :=
  TopPair.ofSubset (X := parameters P) (bad P v₀)

def cochain (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    singularCochainGroup (ZMod 2) (parameters P) ((m + 1) + (p + (m + 1))) :=
  cochainPullback (intoCut P v₀ b) _
    (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T)

theorem closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (parameters P) ((m + 1) + (p + (m + 1)))
      (cochain m p P v₀ b hρ hρr hr hη T) = 0 :=
  cochainPullback_cocycle (intoCut P v₀ b) _ _
    (LocalizedParameterCutCochain.closed m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T hT)

theorem restriction_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    cochainPullback (pair P v₀).map ((m + 1) + (p + (m + 1)))
      (cochain m p P v₀ b hρ hρr hr hη T) = 0 := by
  let i := SupportedCap.subspaceMap (parameters P) (bad P v₀)
  have hz := LocalizedParameterCutCochain.family_zero m p (NorthMeridianEvaluationPoint.target P v₀)
    hρ hρr hr hη (show η + r ≤ (3 / 5 : ℝ) by linarith) T (i ≫ intoCut P v₀ b)
    (fun x => bad_farCarrier (m + 1) P v₀ b x.val x.property)
  change cochainPullback i _ (cochainPullback (intoCut P v₀ b) _ _) = 0
  rw [← pullback_comp]
  exact hz

def relativeCocycle (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.relative (pair P v₀) ((m + 1) + (p + (m + 1))) :=
  (RelativeCupCochain.exists_lift (pair P v₀) _ (cochain m p P v₀ b hρ hρr hr hη T)
    (restriction_zero m p P v₀ b hρ hρr hr hη hr4 hη4 T)).choose

theorem relative_toAmbient (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.toAmbient (pair P v₀) _ (relativeCocycle m p P v₀ b hρ hρr hr hη hr4 hη4 T) =
      cochain m p P v₀ b hρ hρr hr hη T :=
  (RelativeCupCochain.exists_lift (pair P v₀) _ (cochain m p P v₀ b hρ hρr hr hη T)
    (restriction_zero m p P v₀ b hρ hρr hr hη hr4 hη4 T)).choose_spec

theorem relative_closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    RelativeCupCochain.differential (pair P v₀) ((m + 1) + (p + (m + 1)))
      (relativeCocycle m p P v₀ b hρ hρr hr hη hr4 hη4 T) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (pair P v₀) _
  rw [RelativeCupCochain.toAmbient_differential, relative_toAmbient, map_zero]
  exact closed m p P v₀ b hρ hρr hr hη T hT

def relativeClass (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    (pair P v₀).singularCohomology coeff (ZMod 2) coeff ((m + 1) + (p + (m + 1))) :=
  CochainClass.classOf (RelativeCup.cx (pair P v₀)) _ (relativeCocycle m p P v₀ b hρ hρr hr hη hr4 hη4 T)
    (relative_closed m p P v₀ b hρ hρr hr hη hr4 hη4 T hT)

def originalPrimitiveClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :=
  relativeClass m m P v₀ b hρ hρr hr hη hr4 hη4
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (classRepr_isCocycle _ m _)

end
end Finsler.NativePairBoundaryRelativeCut
