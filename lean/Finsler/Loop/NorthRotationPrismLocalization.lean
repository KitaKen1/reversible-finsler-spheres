module

public import Finsler.Loop.NorthMeridianEvaluationPoint
public import Finsler.Loop.StartPointCarrierTimeCupZero
public import Finsler.Loop.NativeThetaCoefficientSixQuarters

/-! Kill the ORIGINAL nine non-north quarter prisms using the SAME
evaluation class localized at the explicit north point. Both ends
of each remaining north quarter also pull the original cochain
back to zero; hence its prism pullback is a genuine closed cochain. -/
@[expose] public section
namespace Finsler.NorthRotationPrismLocalization
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily
open Finsler.MeridianTripleQuarterClocks Finsler.NativeFixedReturnRotationZero Finsler.SobolevShift
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def nonNorthQuarter (q : Fin 3) : Fin 4 := ⟨q.val + 1, by omega⟩

theorem cocycle_excluded_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap (BorelEvaluation.sphere (m + 1))
      (NorthMeridianEvaluationPoint.excluded P v₀)) (m + 1)
      (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) (NorthMeridianEvaluationPoint.target P v₀) hη) = 0 :=
  NorthMeridianEvaluationPoint.cocycle_pullback_zero (by omega) P v₀ hη hη2 _ (fun x => x.property)

theorem piece_excluded {n : ℕ} (P : Sphere n) (v₀ v : equator P) (q : Fin 3) (t : _root_.unitInterval) :
    piece P v₀ v (nonNorthQuarter q) t ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  fin_cases q
  · exact NorthMeridianEvaluationPoint.incoming_excluded P v₀ v t
  · obtain ⟨s, hs⟩ := NativeFixedReturnRotationZero.fixed_piece_range P v₀ v 0 t
    change piece P v₀ v 2 t = meridian P v₀ s at hs
    change piece P v₀ v 2 t ∈ _
    rw [hs]
    exact NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ s
  · obtain ⟨s, hs⟩ := NativeFixedReturnRotationZero.fixed_piece_range P v₀ v 1 t
    change piece P v₀ v 3 t = meridian P v₀ s at hs
    change piece P v₀ v 3 t ∈ _
    rw [hs]
    exact NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ s

theorem quarter_range {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : Fin 3)
    (z : _root_.unitInterval × parameters P) :
    H1FiberBase.point (quarterHomotopy P v₀ k (nonNorthQuarter q) z) ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  change H1FiberBase.point (shiftSphere (NativeH1TripleMeridian.native P v₀ z.2) (clock k (nonNorthQuarter q) z.1)) ∈ _
  rw [NativeTripleSelfEvaluation.point_shift, NativeTripleSelfEvaluation.circle_quarter]
  exact piece_excluded P v₀ _ q z.1

theorem nonnorth_prism_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k q : Fin 3)
    {η ρ r : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    ((quarterHomotopy P v₀ k (nonNorthQuarter q)).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫
      castCochain m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr = 0 :=
  StartPointCarrierTimeCupZero.homotopy_prism_zero m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη
    (NorthMeridianEvaluationPoint.excluded P v₀) (cocycle_excluded_zero m P v₀ hη hη2) _ (quarter_range P v₀ k q)

theorem north_start_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : parameters P) :
    H1FiberBase.point (endpointMap P v₀ k 0 0 z) ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  change H1FiberBase.point (shiftSphere (NativeH1TripleMeridian.native P v₀ z) (clock k 0 0)) ∈ _
  rw [NativeTripleSelfEvaluation.point_shift, NativeTripleSelfEvaluation.circle_quarter]
  have he : piece P v₀ (NativeTripleSelfEvaluation.directions z k) 0 0 = P :=
    (RationalSphereArc.arc (outgoing P (NativeTripleSelfEvaluation.directions z k))).source
  rw [he]
  apply Or.inl
  have hv : ⟪(v₀.val : Ambient n), (P : Ambient n)⟫ = 0 := (real_inner_comm _ _).trans v₀.property
  exact hv.ge

theorem north_finish_excluded {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : parameters P) :
    H1FiberBase.point (endpointMap P v₀ k 0 1 z) ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  change H1FiberBase.point (shiftSphere (NativeH1TripleMeridian.native P v₀ z) (clock k 0 1)) ∈ _
  rw [NativeTripleSelfEvaluation.point_shift, NativeTripleSelfEvaluation.circle_quarter]
  have he : piece P v₀ (NativeTripleSelfEvaluation.directions z k) 0 1 = (NativeTripleSelfEvaluation.directions z k).val :=
    (RationalSphereArc.arc (outgoing P (NativeTripleSelfEvaluation.directions z k))).target
  rw [he]
  exact Or.inr (NativeTripleSelfEvaluation.directions z k).property.le

theorem north_endpoints_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    {η ρ r : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    cochainPullback (endpointMap P v₀ k 0 0) (3 * m + 1)
      (castCochain m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr) = 0 ∧
    cochainPullback (endpointMap P v₀ k 0 1) (3 * m + 1)
      (castCochain m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr) = 0 := by
  constructor
  · exact StartPointCarrierTimeCupZero.cast_family_zero m _ hρ hρr hr hη _
      (cocycle_excluded_zero m P v₀ hη hη2) _ (north_start_excluded P v₀ k)
  · exact StartPointCarrierTimeCupZero.cast_family_zero m _ hρ hρr hr hη _
      (cocycle_excluded_zero m P v₀ hη hη2) _ (north_finish_excluded P v₀ k)

def northCochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    {η ρ r : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    singularCochainGroup (ZMod 2) (parameters P) (3 * m) :=
  ((quarterHomotopy P v₀ k 0).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫
    castCochain m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr

theorem north_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    {η ρ r : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    cochainCoboundary (ZMod 2) (parameters P) (3 * m) (northCochain m P v₀ k hη hρ hρr hr) = 0 := by
  let ψ := castCochain m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr
  have hc := cast_closed m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr
  change (chains (Loops (m + 1))).d (3 * m + 2) (3 * m + 1) ≫ ψ = 0 at hc
  obtain ⟨h0, h1⟩ := north_endpoints_zero m P v₀ k hη hη2 hρ hρr hr
  change (SSet.chainComplexMap (TopCat.toSSet.map (endpointMap P v₀ k 0 0)) coeff).f (3 * m + 1) ≫ ψ = 0 at h0
  change (SSet.chainComplexMap (TopCat.toSSet.map (endpointMap P v₀ k 0 1)) coeff).f (3 * m + 1) ≫ ψ = 0 at h1
  have he := ((quarterHomotopy P v₀ k 0).toSSet.chainComplexMap coeff).comm (3 * m + 1)
  simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at he
  have hp := congrArg (fun f => f ≫ ψ) he
  simp only [Preadditive.add_comp, Category.assoc, hc, h0, h1, comp_zero, add_zero] at hp
  change (chains (parameters P)).d (3 * m + 1) (3 * m) ≫
    ((quarterHomotopy P v₀ k 0).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ = 0
  exact hp.symm

end
end Finsler.NorthRotationPrismLocalization
