module

public import Finsler.Geometry.SphereRetraction

/-! The actual Finsler energy as an ambient position--velocity Lagrangian.
The sphere tangent retraction supplies the extension, rather than a new
smoothness assumption. Its chain rule gives the usual two terms of the first
variation for every smooth periodic tangent test field. Downstream modules
handle integration by parts, the pointwise implication and equivalence with
ordinary coordinate geodesics for regular smooth loops. H¹ remains open. -/

@[expose] public section

namespace Finsler.AmbientLagrangian

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.SphereRetraction Finsler.SphereVariation
open TauCeti.Manifold Function
open scoped Manifold ContDiff Interval

noncomputable section

variable {n : ℕ}

/-- The density is F², matching the actual energy already defined on loops. -/
def lagrangian (F : ReversibleMetric n) (z : Ambient n × Ambient n) : ℝ :=
  F.value (lift z) ^ 2

def slitDomain (n : ℕ) : Set (Ambient n × Ambient n) :=
  {z | z.1 ≠ 0 ∧ lift z ∈ slitBundle n}

theorem lagrangian_smoothAt (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z ∈ slitDomain n) : ContDiffAt ℝ ∞ (lagrangian F) z :=
  (((value_smoothAt F (lift z) hz.2).comp z
    (lift_smoothAt hz.1)).contDiffAt.pow 2)

theorem lagrangian_smoothOn (F : ReversibleMetric n) :
    ContDiffOn ℝ ∞ (lagrangian F) (slitDomain n) :=
  fun _ hz => (lagrangian_smoothAt F hz).contDiffWithinAt

theorem lagrangian_ambientPair (F : ReversibleMetric n) (p : Total n) :
    lagrangian F (ambientPair p) = F.value p ^ 2 := by
  rw [lagrangian, lift_ambientPair]

theorem ambientJet_eq_ambientPair (V : SmoothVariation n) (z : ℝ × ℝ) :
    ambientJet V z = ambientPair (Finsler.FirstVariation.velocityLift V z) := rfl

theorem ambientJet_smooth (V : SmoothVariation n) : ContDiff ℝ ∞ (ambientJet V) :=
  ((inclusion_smooth n).comp V.smooth).contDiff.prodMk
    ((ambientVector_smooth n).comp (Finsler.FirstVariation.velocityLift_smooth V)).contDiff

def loopJet (γ : SmoothLoop n) (t : ℝ) : Ambient n × Ambient n :=
  ambientPair (Finsler.LoopEnergy.velocityLift γ t)

theorem ambientJet_eq_loopJet (V : SmoothVariation n) (s t : ℝ) :
    ambientJet V (s, t) = loopJet (loopAt V s) t := by
  rw [ambientJet_eq_ambientPair, Finsler.FirstVariation.velocityLift_eq_loopVelocity]
  rfl

theorem loopJet_smooth (γ : SmoothLoop n) : ContDiff ℝ ∞ (loopJet γ) := by
  convert! (ambientJet_smooth (constantVariation γ)).comp
    ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id) using 1
  funext t
  rw [Function.comp_apply, ambientJet_eq_loopJet, loopAt_constantVariation]
  rfl

theorem loopJet_periodic (γ : SmoothLoop n) : Periodic (loopJet γ) 1 := by
  have he : (γ ∘ fun t : ℝ => t + 1) = (γ : ℝ → Sphere n) := funext γ.periodic
  intro t
  have h := Finsler.LoopEnergy.velocityLift_comp γ ((hasDerivAt_id t).add_const 1)
    (γ.smooth.mdifferentiableAt (by simp))
  simp only [he, id_eq, one_smul, ← curveVelocityLift_apply] at h
  exact congrArg ambientPair h.symm

theorem lagrangian_ambientJet (F : ReversibleMetric n) (V : SmoothVariation n)
    (z : ℝ × ℝ) :
    lagrangian F (ambientJet V z) = Finsler.FirstVariation.density F V z := by
  rw [ambientJet_eq_ambientPair, lagrangian_ambientPair]
  rfl

theorem ambientJet_mem_slitDomain (V : SmoothVariation n) {z : ℝ × ℝ}
    (hz : z ∈ Finsler.FirstVariation.regularDomain V) :
    ambientJet V z ∈ slitDomain n := by
  refine ⟨ne_zero_of_mem_unit_sphere (V.family z), ?_⟩
  rw [ambientJet_eq_ambientPair, lift_ambientPair]
  exact hz

def positionDifferential (F : ReversibleMetric n) (z : Ambient n × Ambient n) :
    Ambient n →L[ℝ] ℝ :=
  (fderiv ℝ (lagrangian F) z).comp (ContinuousLinearMap.inl ℝ (Ambient n) (Ambient n))

def velocityDifferential (F : ReversibleMetric n) (z : Ambient n × Ambient n) :
    Ambient n →L[ℝ] ℝ :=
  (fderiv ℝ (lagrangian F) z).comp (ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n))

theorem differential_split (F : ReversibleMetric n) (z : Ambient n × Ambient n)
    (a b : Ambient n) :
    fderiv ℝ (lagrangian F) z (a, b) =
      positionDifferential F z a + velocityDifferential F z b := by
  change _ = fderiv ℝ (lagrangian F) z (a, 0) + fderiv ℝ (lagrangian F) z (0, b)
  rw [← map_add]
  simp

variable {γ : SmoothLoop n}

theorem ambientJet_variation_zero (η : SmoothTangentField γ) (t : ℝ) :
    ambientJet (variation η) (0, t) = loopJet γ t := by
  rw [ambientJet_eq_loopJet, loopAt_variation_zero]

theorem loopJet_mem_slitDomain (γ : SmoothLoop n) (hreg : Regular γ) (t : ℝ) :
    loopJet γ t ∈ slitDomain n := by
  refine ⟨?_, ?_⟩
  · simpa only [loopJet, ambientPair, Finsler.LoopEnergy.velocityLift,
      curveVelocityLift_apply] using ne_zero_of_mem_unit_sphere (γ t)
  rw [loopJet, lift_ambientPair]
  simpa only [Finsler.LoopEnergy.velocityLift, slitBundle, Set.mem_ofPred_eq,
    curveVelocityLift_apply] using hreg t

theorem density_variation_hasDerivAt (F : ReversibleMetric n) (hreg : Regular γ)
    (η : SmoothTangentField γ) (t : ℝ) :
    HasDerivAt (fun s => Finsler.FirstVariation.density F (variation η) (s, t))
      (fderiv ℝ (lagrangian F) (ambientJet (variation η) (0, t))
        (η.value t, deriv η.value t)) 0 := by
  have hr : Regular (loopAt (variation η) 0) := (loopAt_variation_zero η).symm ▸ hreg
  have hz := (Finsler.FirstVariation.mem_regularDomain_iff (variation η) 0 t).mpr (hr t)
  have hd := (lagrangian_smoothAt F (ambientJet_mem_slitDomain (variation η) hz)).differentiableAt
    (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt 0 (ambientJet_variation_hasDerivAt η t)
  simpa only [Function.comp_def, lagrangian_ambientJet] using hh

theorem partial_density_variation_eq (F : ReversibleMetric n) (hreg : Regular γ)
    (η : SmoothTangentField γ) (t : ℝ) :
    fderiv ℝ (Finsler.FirstVariation.density F (variation η)) (0, t) (1, 0) =
      positionDifferential F (ambientJet (variation η) (0, t)) (η.value t) +
      velocityDifferential F (ambientJet (variation η) (0, t)) (deriv η.value t) := by
  have hr : Regular (loopAt (variation η) 0) := (loopAt_variation_zero η).symm ▸ hreg
  have hz := (Finsler.FirstVariation.mem_regularDomain_iff (variation η) 0 t).mpr (hr t)
  have hd := ((Finsler.FirstVariation.density_smoothOn F (variation η)) (0, t) hz).contDiffAt
    ((Finsler.FirstVariation.regularDomain_isOpen (variation η)).mem_nhds hz)
  have hh := hasDerivAt_parameterCurve (hd.differentiableAt (by simp))
  rw [← differential_split]
  simpa only [timeFDeriv_apply] using hh.unique (density_variation_hasDerivAt F hreg η t)

theorem firstVariation_position_velocity (F : ReversibleMetric n) (hreg : Regular γ)
    (η : SmoothTangentField γ) :
    Finsler.FirstVariation.firstVariation F (variation η) 0 =
      ∫ t in 0..1,
        positionDifferential F (ambientJet (variation η) (0, t)) (η.value t) +
        velocityDifferential F (ambientJet (variation η) (0, t)) (deriv η.value t) := by
  apply intervalIntegral.integral_congr
  intro t _
  exact partial_density_variation_eq F hreg η t

theorem stationary_position_velocity_zero (F : ReversibleMetric n) (hreg : Regular γ)
    (hstat : Stationary F γ) (η : SmoothTangentField γ) :
    (∫ t in 0..1,
      positionDifferential F (ambientJet (variation η) (0, t)) (η.value t) +
      velocityDifferential F (ambientJet (variation η) (0, t)) (deriv η.value t)) = 0 := by
  rw [← firstVariation_position_velocity F hreg η]
  exact stationary_explicit_firstVariation_zero F hreg hstat η

theorem firstVariation_loopJet (F : ReversibleMetric n) (hreg : Regular γ)
    (η : SmoothTangentField γ) :
    Finsler.FirstVariation.firstVariation F (variation η) 0 =
      ∫ t in 0..1,
        positionDifferential F (loopJet γ t) (η.value t) +
        velocityDifferential F (loopJet γ t) (deriv η.value t) := by
  simpa only [ambientJet_variation_zero] using firstVariation_position_velocity F hreg η

theorem stationary_loopJet_zero (F : ReversibleMetric n) (hreg : Regular γ)
    (hstat : Stationary F γ) (η : SmoothTangentField γ) :
    (∫ t in 0..1,
      positionDifferential F (loopJet γ t) (η.value t) +
      velocityDifferential F (loopJet γ t) (deriv η.value t)) = 0 := by
  simpa only [ambientJet_variation_zero] using stationary_position_velocity_zero F hreg hstat η

theorem positionDifferential_loopJet_smooth (F : ReversibleMetric n) (hreg : Regular γ) :
    ContDiff ℝ ∞ (fun t => positionDifferential F (loopJet γ t)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (((lagrangian_smoothAt F (loopJet_mem_slitDomain γ hreg t)).fderiv_right
    (m := ∞) (by simp)).comp t (loopJet_smooth γ).contDiffAt).clm_comp contDiffAt_const

theorem velocityDifferential_loopJet_smooth (F : ReversibleMetric n) (hreg : Regular γ) :
    ContDiff ℝ ∞ (fun t => velocityDifferential F (loopJet γ t)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (((lagrangian_smoothAt F (loopJet_mem_slitDomain γ hreg t)).fderiv_right
    (m := ∞) (by simp)).comp t (loopJet_smooth γ).contDiffAt).clm_comp contDiffAt_const

end

end Finsler.AmbientLagrangian
