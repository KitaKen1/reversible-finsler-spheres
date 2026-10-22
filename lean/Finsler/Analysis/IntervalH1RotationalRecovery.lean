module

public import Finsler.Analysis.IntervalH1RotationalVariation

/-! Finite recovery of the actual tangential velocity covector from rotational
momenta. Under TangentCritical the recovered covector is continuous on [0,1],
has periodic endpoint traces and is independent of the orthonormal basis.
Radial annihilation of the full velocity differential is not required.
Zero exclusion, Legendre inversion and smooth regularity are separate. -/

@[expose] public section

namespace Finsler.SobolevRotationalRecovery

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevRotationalVariation Finsler.SobolevCurveVariation
open Finsler.SobolevEnergyDifferential Finsler.AmbientLagrangian
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- A fixed rank-two skew operator. No differentiability of the loop enters here. -/
def planeRotation (a b : Ambient n) : Ambient n →L[ℝ] Ambient n :=
  (innerSL ℝ b).smulRight a - (innerSL ℝ a).smulRight b

theorem planeRotation_apply (a b x : Ambient n) :
    planeRotation a b x = ⟪b, x⟫ • a - ⟪a, x⟫ • b := rfl

theorem planeRotation_isRotation (a b : Ambient n) :
    InfinitesimalRotation (planeRotation a b) := by
  intro x
  rw [planeRotation_apply, inner_sub_right, inner_smul_right, inner_smul_right,
    real_inner_comm x a, real_inner_comm x b]
  ring

/-- Remove the radial component of a covector at a unit sphere point. -/
def tangentCovector (q : Ambient n) (p : Ambient n →L[ℝ] ℝ) :
    Ambient n →L[ℝ] ℝ := p - p q • innerSL ℝ q

theorem tangentCovector_apply (q x : Ambient n) (p : Ambient n →L[ℝ] ℝ) :
    tangentCovector q p x = p x - p q * ⟪q, x⟫ := rfl

theorem tangentCovector_apply_of_orthogonal (q x : Ambient n)
    (p : Ambient n →L[ℝ] ℝ) (hx : ⟪q, x⟫ = 0) :
    tangentCovector q p x = p x := by
  simp [tangentCovector_apply, hx]

theorem tangentCovector_annihilates (q : Ambient n) (p : Ambient n →L[ℝ] ℝ)
    (hq : ‖q‖ = 1) : tangentCovector q p q = 0 := by
  rw [tangentCovector_apply, real_inner_self_eq_norm_sq, hq]
  ring

theorem tangentCovector_rotation (q : Ambient n) (p : Ambient n →L[ℝ] ℝ)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A) :
    tangentCovector q p (A q) = p (A q) :=
  tangentCovector_apply_of_orthogonal q (A q) p (hA q)

theorem covector_planeRotation (p : Ambient n →L[ℝ] ℝ) (a b q : Ambient n) :
    p (planeRotation a b q) = ⟪b, q⟫ * p a - ⟪a, q⟫ * p b := by
  rw [planeRotation_apply, map_sub, map_smul, map_smul]
  rfl

theorem basis_rotation_recovery {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (q : Ambient n)
    (p : Ambient n →L[ℝ] ℝ) (hq : ‖q‖ = 1) (i : ι) :
    (∑ j, ⟪b j, q⟫ * p (planeRotation (b i) (b j) q)) =
      tangentCovector q p (b i) := by
  have hnorm : (∑ j, ⟪b j, q⟫ * ⟪b j, q⟫) = 1 := by
    simpa only [real_inner_comm q, real_inner_self_eq_norm_sq, hq, one_pow] using
      b.sum_inner_mul_inner q q
  have hp : (∑ j, ⟪b j, q⟫ * p (b j)) = p q := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg p (b.sum_repr' q)
  simp_rw [covector_planeRotation]
  calc
    _ = (∑ j, ⟪b j, q⟫ * ⟪b j, q⟫) * p (b i) -
        ⟪b i, q⟫ * (∑ j, ⟪b j, q⟫ * p (b j)) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = tangentCovector q p (b i) := by
      rw [hnorm, hp, tangentCovector_apply, real_inner_comm q (b i)]
      ring

theorem basis_covector_reconstruction {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (p : Ambient n →L[ℝ] ℝ) :
    (∑ i, p (b i) • innerSL ℝ (b i)) = p := by
  ext x
  simpa only [sum_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, map_sum,
    map_smul, mul_comm] using congrArg p (b.sum_repr' x)

/-- Assemble a covector from the finitely many continuous scalar momenta. -/
def recoveredCovector {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) : Ambient n →L[ℝ] ℝ :=
  ∑ i, (∑ j, ⟪b j, continuousRepresentative (u.data : Space n) t⟫ *
    momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t) •
      innerSL ℝ (b i)

theorem recoveredCovector_continuousOn {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) :
    ContinuousOn (recoveredCovector b F u hc) (Icc 0 1) := by
  classical
  apply continuousOn_finsetSum
  intro i _
  have hcoeff : ContinuousOn (fun t => ∑ j,
      ⟪b j, continuousRepresentative (u.data : Space n) t⟫ *
        momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t)
      (Icc 0 1) := by
    apply continuousOn_finsetSum
    intro j _
    exact ((innerSL ℝ (b j)).continuous.comp_continuousOn
      (continuousRepresentative_continuousOn (u.data : Space n))).mul
        (momentumRepresentative_continuousOn F u (planeRotation_isRotation (b i) (b j)) hc)
  exact hcoeff.fun_smul (continuousOn_const (c := innerSL ℝ (b i)))

theorem recoveredCovector_ae {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) :
    recoveredCovector b F u hc =ᵐ[intervalMeasure] fun t =>
      tangentCovector (continuousRepresentative (u.data : Space n) t)
        (velocityDifferential F (weakJet u t)) := by
  classical
  have hm : ∀ᵐ t ∂intervalMeasure, ∀ i j,
      momentum F u (planeRotation (b i) (b j)) t =
        momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t :=
    eventually_all.mpr fun i => eventually_all.mpr fun j =>
      momentum_ae_representative F u (planeRotation_isRotation (b i) (b j)) hc
  filter_upwards [hm, ae_restrict_mem measurableSet_Ioo] with t hm ht
  unfold recoveredCovector
  calc
    _ = ∑ i, tangentCovector (continuousRepresentative (u.data : Space n) t)
        (velocityDifferential F (weakJet u t)) (b i) • innerSL ℝ (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp_rw [← hm i]
      exact basis_rotation_recovery b _ _
        (u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩) i
    _ = _ := basis_covector_reconstruction b _

theorem recoveredCovector_annihilates {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) (t : ClosedInterval) :
    recoveredCovector b F u hc t (continuousRepresentative (u.data : Space n) t) = 0 := by
  have he : (fun s => recoveredCovector b F u hc s
      (continuousRepresentative (u.data : Space n) s)) =ᵐ[intervalMeasure] fun _ => 0 := by
    filter_upwards [recoveredCovector_ae b F u hc,
      ae_restrict_mem measurableSet_Ioo] with s hs ht
    rw [hs]
    exact tangentCovector_annihilates _ _
      (u.sphere_constraint ⟨s, Ioo_subset_Icc_self ht⟩)
  change _ =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] _ at he
  rw [restrict_Ioo_eq_restrict_Icc] at he
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) he
    ((recoveredCovector_continuousOn b F u hc).clm_apply
      (continuousRepresentative_continuousOn (u.data : Space n))) continuousOn_const t.property

theorem recoveredCovector_rotation {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A) (t : ClosedInterval) :
    recoveredCovector b F u hc t (A (continuousRepresentative (u.data : Space n) t)) =
      momentumRepresentative F u hA hc t := by
  symm
  apply momentumRepresentative_unique F u hA hc
    ((recoveredCovector_continuousOn b F u hc).clm_apply
      (A.continuous.comp_continuousOn (continuousRepresentative_continuousOn (u.data : Space n))))
    _ t.property
  filter_upwards [recoveredCovector_ae b F u hc] with s hs
  simp only [Function.comp_apply]
  rw [hs, tangentCovector_rotation _ _ hA]
  rfl

theorem recoveredCovector_velocity_ae {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) :
    (fun t => recoveredCovector b F u hc t (velocity (u.data : Space n) t)) =ᵐ[intervalMeasure]
      fun t => velocityDifferential F (weakJet u t) (velocity (u.data : Space n) t) := by
  filter_upwards [recoveredCovector_ae b F u hc, weakVelocity_orthogonal_ae u] with t ht hv
  rw [ht, tangentCovector_apply_of_orthogonal _ _ _ hv]

theorem recoveredCovector_periodic_trace {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) :
    recoveredCovector b F u hc 1 = recoveredCovector b F u hc 0 := by
  classical
  have hq : continuousRepresentative (u.data : Space n) 1 =
      continuousRepresentative (u.data : Space n) 0 :=
    (mem_periodicSubmodule_iff (u.data : Space n)).mp u.data.property
  unfold recoveredCovector
  simp_rw [hq, momentumRepresentative_periodic_trace F u _ hc]

theorem recoveredCovector_basis_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (Ambient n)) (c : OrthonormalBasis κ ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (t : ClosedInterval) : recoveredCovector b F u hc t = recoveredCovector c F u hc t := by
  have he := (recoveredCovector_ae b F u hc).trans (recoveredCovector_ae c F u hc).symm
  change _ =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] _ at he
  rw [restrict_Ioo_eq_restrict_Icc] at he
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) he
    (recoveredCovector_continuousOn b F u hc) (recoveredCovector_continuousOn c F u hc) t.property

end

end Finsler.SobolevRotationalRecovery
