module

public import Finsler.Analysis.IntervalH1SmoothRegularity
public import Finsler.Analysis.IntervalH1CircleRepresentative

/-! Readback of positive-energy tangent-critical actual H¹ sphere loops as ordinary
smooth closed geodesics. `JetData` packages a position, a continuous velocity and
plane momenta on an open set of times whose momenta are primitives of the force on
the jet and whose tangent Legendre covector is assembled from the momenta; an
induction through the smooth local Legendre inverse makes such data C^∞. The periodic
real representative, the periodic extension of the continuous velocity and the
rotational momenta extended by integrating the periodic force form such data on all
of ℝ: the derivative at integer times is glued from the two one-sided derivatives,
and the momentum extension is periodic because the force integrates to zero over a
period. The resulting C^∞ periodic sphere loop is regular, and the momentum identity
for every fixed rotation gives the constrained ambient Euler equation, hence
variational stationarity. Realization of every tangent direction by actual curves and
comparison with finite-cut critical points remain separate. -/

@[expose] public section

namespace Finsler.SobolevGeodesicReadback

open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientLagrangian
open Finsler.SobolevRotationalRecovery Finsler.SobolevSmoothRegularity
open Set Filter Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Covector assembled from plane momenta along a position path. -/
def assembledCovector (b : OrthonormalBasis ι ℝ (Ambient n)) (q : ℝ → Ambient n)
    (P : ι → ι → ℝ → ℝ) (t : ℝ) : Ambient n →L[ℝ] ℝ :=
  ∑ i, (∑ j, ⟪b j, q t⟫ * P i j t) • innerSL ℝ (b i)

theorem smoothForce_contDiffAt_of_slit (F : ReversibleMetric n) {q v : ℝ → Ambient n}
    (A : Ambient n →L[ℝ] Ambient n) {k : ℕ} {t : ℝ} (hz : (q t, v t) ∈ slitDomain n)
    (hq : ContDiffAt ℝ k q t) (hv : ContDiffAt ℝ k v t) :
    ContDiffAt ℝ k (smoothForce F q v A) t := by
  have hL := lagrangian_smoothAt F hz
  have hfd : ContDiffAt ℝ k (fderiv ℝ (lagrangian F)) (q t, v t) :=
    hL.fderiv_right (m := k) (by exact_mod_cast le_top)
  have hpair : ContDiffAt ℝ k (fun s => (q s, v s)) t := hq.prodMk hv
  have hdir : ContDiffAt ℝ k (fun s => (A (q s), A (v s))) t :=
    (A.contDiff.contDiffAt.comp t hq).prodMk (A.contDiff.contDiffAt.comp t hv)
  exact (hfd.comp t hpair).clm_apply hdir

theorem assembledCovector_contDiffAt (b : OrthonormalBasis ι ℝ (Ambient n))
    {q : ℝ → Ambient n} {P : ι → ι → ℝ → ℝ} {k : ℕ} {t : ℝ} (hq : ContDiffAt ℝ k q t)
    (hP : ∀ i j, ContDiffAt ℝ k (P i j) t) : ContDiffAt ℝ k (assembledCovector b q P) t := by
  classical
  unfold assembledCovector
  apply ContDiffAt.sum
  intro i _
  exact (ContDiffAt.sum fun j _ => (contDiffAt_const.inner ℝ hq).mul (hP i j)).smul
    contDiffAt_const

/-- Position, velocity and plane momenta satisfying the weak geodesic structure
on an open set of times. -/
structure JetData (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (U : Set ℝ) where
  q : ℝ → Ambient n
  v : ℝ → Ambient n
  P : ι → ι → ℝ → ℝ
  hasDerivAt_q : ∀ t ∈ U, HasDerivAt q (v t) t
  continuousOn_v : ContinuousOn v U
  hasDerivAt_P : ∀ i j, ∀ t ∈ U,
    HasDerivAt (P i j) (smoothForce F q v (planeRotation (b i) (b j)) t) t
  unit : ∀ t ∈ U, ‖q t‖ = 1
  tangent : ∀ t ∈ U, ⟪q t, v t⟫ = 0
  nonzero : ∀ t ∈ U, v t ≠ 0
  legendre : ∀ t ∈ U,
    legendreExt F (q t, v t) = (q t, covectorVectorL n (assembledCovector b q P t))

section JetDataTheory

variable {b : OrthonormalBasis ι ℝ (Ambient n)} {F : ReversibleMetric n} {U : Set ℝ}
  (D : JetData b F U)

theorem jet_slit {t : ℝ} (ht : t ∈ U) : (D.q t, D.v t) ∈ slitDomain n :=
  tangent_mem_slitDomain (D.unit t ht) (D.tangent t ht) (D.nonzero t ht)

theorem jet_v_contDiffAt_nat (hU : IsOpen U) (k : ℕ) : ∀ t ∈ U, ContDiffAt ℝ k D.v t := by
  induction k with
  | zero =>
    intro t ht
    exact contDiffAt_zero.mpr ⟨U, hU.mem_nhds ht, D.continuousOn_v⟩
  | succ k ih =>
    intro t₀ ht₀
    have hq1 (y : ℝ) (hy : y ∈ U) : ContDiffAt ℝ (k + 1) D.q y :=
      contDiffAt_succ_of_hasDerivAt (Filter.eventually_of_mem (hU.mem_nhds hy) D.hasDerivAt_q)
        (ih y hy)
    have hforce (A : Ambient n →L[ℝ] Ambient n) (y : ℝ) (hy : y ∈ U) :
        ContDiffAt ℝ k (smoothForce F D.q D.v A) y :=
      smoothForce_contDiffAt_of_slit F A (jet_slit D hy)
        ((hq1 y hy).of_le (by exact_mod_cast Nat.le_succ k)) (ih y hy)
    have hP (i j : ι) : ContDiffAt ℝ (k + 1) (D.P i j) t₀ :=
      contDiffAt_succ_of_hasDerivAt
        (Filter.eventually_of_mem (hU.mem_nhds ht₀) (D.hasDerivAt_P i j)) (hforce _ t₀ ht₀)
    have hQ := assembledCovector_contDiffAt b (hq1 t₀ ht₀) hP
    obtain ⟨g, hg, hinv⟩ := exists_smooth_local_inverse F (D.unit t₀ ht₀) (D.tangent t₀ ht₀)
      (D.nonzero t₀ ht₀)
    have hpath : ContinuousAt (fun t => (D.q t, D.v t)) t₀ :=
      (D.hasDerivAt_q t₀ ht₀).continuousAt.prodMk
        (D.continuousOn_v.continuousAt (hU.mem_nhds ht₀))
    have hev : D.v =ᶠ[𝓝 t₀]
        fun t => (g (D.q t, covectorVectorL n (assembledCovector b D.q D.P t))).2 := by
      filter_upwards [hpath.eventually hinv, hU.mem_nhds ht₀] with t ht hmem
      rw [← D.legendre t hmem, ht]
    have hg' : ContDiffAt ℝ ∞ g
        (D.q t₀, covectorVectorL n (assembledCovector b D.q D.P t₀)) := by
      rw [← D.legendre t₀ ht₀]
      exact hg
    have hcomp : ContDiffAt ℝ (k + 1)
        (fun t => (g (D.q t, covectorVectorL n (assembledCovector b D.q D.P t))).2) t₀ :=
      contDiffAt_snd.comp t₀ ((hg'.of_le (by exact_mod_cast le_top)).comp t₀
        ((hq1 t₀ ht₀).prodMk ((covectorVectorL n).contDiff.contDiffAt.comp t₀ hQ)))
    have h := hcomp.congr_of_eventuallyEq hev
    exact_mod_cast h

theorem jet_v_contDiffAt (hU : IsOpen U) {t : ℝ} (ht : t ∈ U) : ContDiffAt ℝ ∞ D.v t :=
  contDiffAt_infty.mpr fun k => jet_v_contDiffAt_nat D hU k t ht

theorem jet_q_contDiffAt (hU : IsOpen U) {t : ℝ} (ht : t ∈ U) : ContDiffAt ℝ ∞ D.q t := by
  apply contDiffAt_infty.mpr
  intro k
  have h := contDiffAt_succ_of_hasDerivAt
    (Filter.eventually_of_mem (hU.mem_nhds ht) D.hasDerivAt_q)
    ((jet_v_contDiffAt D hU ht).of_le (by exact_mod_cast le_top) : ContDiffAt ℝ k D.v t)
  exact h.of_le (by exact_mod_cast Nat.le_succ k)

end JetDataTheory

/-! ### The periodic extension of a positive tangent-critical loop -/

section Periodic

open MeasureTheory Finsler.IntervalSobolev Finsler.SobolevRotationalVariation
open Finsler.SobolevRotationalBounds Finsler.SobolevZeroExclusion Finsler.SobolevCurveVariation
open Finsler.SobolevEnergyDifferential Finsler.SobolevEnergy Finsler.SobolevVelocityContinuity
open Finsler.SobolevCircleRepresentative
open scoped Interval

variable (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n) (u : SphereLoop n)
  (hc : TangentCritical F u)

local notation "qR" => continuousRepresentative (u.data : Space n)
local notation "vR" => velocityRep b F u hc

/-- The periodic real representative of the loop. -/
def qP (t : ℝ) : Ambient n := realMap u.data t

/-- The periodic extension of the continuous velocity representative. -/
def vP (t : ℝ) : Ambient n := vR (Int.fract t)

theorem qP_eq_of_sub_mem {t : ℝ} (k : ℤ) (ht : t - k ∈ Icc (0 : ℝ) 1) : qP u t = qR (t - k) := by
  have h := (realMap_periodic u.data).sub_int_mul_eq (x := t) k
  rw [mul_one] at h
  unfold qP
  rw [← h]
  exact realMap_eqOn u.data ht

theorem qP_eq_fract (t : ℝ) : qP u t = qR (Int.fract t) :=
  qP_eq_of_sub_mem u ⌊t⌋ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

theorem fract_mem_Icc (t : ℝ) : Int.fract t ∈ Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

theorem vP_continuous : Continuous (vP b F u hc) := by
  have h := ContinuousOn.comp_fract (s := id) (f := fun (_ : ℝ) (x : ℝ) => vR x)
    ((velocityRep_continuous b F u hc).comp continuous_snd).continuousOn continuous_id
    (fun _ => (velocityRep_periodic b F u hc).symm)
  exact h

theorem vP_eq_on {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : vP b F u hc t = vR t := by
  unfold vP
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1, Int.fract_one, ← velocityRep_periodic b F u hc]
  · rw [Int.fract_eq_self.mpr ⟨ht.1, h1⟩]

theorem qP_hasDerivAt (t : ℝ) : HasDerivAt (qP u) (vP b F u hc t) t := by
  set k : ℤ := ⌊t⌋ with hk
  have hfr : Int.fract t = t - k := rfl
  rcases eq_or_lt_of_le (Int.fract_nonneg t) with h0 | hpos
  · -- integer time: glue the two one-sided derivatives
    have htk : t = k := by linarith [hfr ▸ h0.symm]
    have hv : vP b F u hc t = vR 0 := by
      unfold vP
      rw [← h0]
    rw [hv]
    have hright0 := (representative_hasDerivWithinAt b F u hc
      (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE zero_lt_one)
    have hleft1 := (representative_hasDerivWithinAt b F u hc
      (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE zero_lt_one)
    rw [velocityRep_periodic b F u hc] at hleft1
    have hshiftR : HasDerivWithinAt (fun x : ℝ => x - k) 1 (Ici t) t :=
      ((hasDerivAt_id' t).sub_const (k : ℝ)).hasDerivWithinAt
    have hshiftL : HasDerivWithinAt (fun x : ℝ => x - (k - 1 : ℤ)) 1 (Iic t) t :=
      ((hasDerivAt_id' t).sub_const ((k - 1 : ℤ) : ℝ)).hasDerivWithinAt
    have hR : HasDerivWithinAt (fun x => qR (x - k)) (vR 0) (Ici t) t := by
      have h := HasDerivWithinAt.scomp t (g₁ := qR) (h := fun x : ℝ => x - k)
        (by simpa [htk] using hright0) hshiftR (fun x hx => by
          simp only [mem_Ici] at hx ⊢
          linarith)
      simpa only [one_smul, Function.comp_def] using h
    have hL : HasDerivWithinAt (fun x => qR (x - (k - 1 : ℤ))) (vR 0) (Iic t) t := by
      have h := HasDerivWithinAt.scomp t (g₁ := qR) (h := fun x : ℝ => x - (k - 1 : ℤ))
        (by
          have h1 : t - ((k - 1 : ℤ) : ℝ) = 1 := by push_cast; linarith
          rw [h1]
          exact hleft1) hshiftL (fun x hx => by
          simp only [mem_Iic] at hx ⊢
          push_cast
          linarith)
      simpa only [one_smul, Function.comp_def] using h
    have hR' : HasDerivWithinAt (qP u) (vR 0) (Ici t) t := by
      apply hR.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin, Ico_mem_nhdsGE (show t < t + 1 by linarith)]
          with x _ hx
        exact qP_eq_of_sub_mem u k ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact qP_eq_of_sub_mem u k ⟨by linarith, by linarith⟩
    have hL' : HasDerivWithinAt (qP u) (vR 0) (Iic t) t := by
      apply hL.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsLE (show t - 1 < t by linarith)]
          with x _ hx
        exact qP_eq_of_sub_mem u (k - 1) ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
      · exact qP_eq_of_sub_mem u (k - 1) ⟨by push_cast; linarith, by push_cast; linarith⟩
    have h := hL'.union hR'
    rw [Iic_union_Ici] at h
    exact hasDerivWithinAt_univ.mp h
  · -- non-integer time: translate the interior derivative
    have hlt : Int.fract t < 1 := Int.fract_lt_one t
    have hin : t - k ∈ Ioo (0 : ℝ) 1 := ⟨by rw [← hfr]; exact hpos, by rw [← hfr]; exact hlt⟩
    have hd := HasDerivAt.comp_sub_const t (k : ℝ) (representative_hasDerivAt b F u hc hin)
    have hv : vP b F u hc t = vR (t - k) := rfl
    rw [hv]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (show (k : ℝ) < t by linarith [hin.1])
      (show t < k + 1 by linarith [hin.2])] with x hx
    exact qP_eq_of_sub_mem u k ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem qP_continuous : Continuous (qP u) := (realMap u.data).continuous

theorem qP_unit (t : ℝ) : ‖qP u t‖ = 1 := by
  rw [qP_eq_fract]
  exact u.sphere_constraint ⟨_, fract_mem_Icc t⟩

theorem vP_tangent (t : ℝ) : ⟪qP u t, vP b F u hc t⟫ = 0 := by
  rw [qP_eq_fract]
  exact velocityRep_tangent b F u hc (fract_mem_Icc t)

theorem vP_ne_zero (hE : 0 < energy F u) (t : ℝ) : vP b F u hc t ≠ 0 :=
  velocityRep_ne_zero b F u hc hE (fract_mem_Icc t)

theorem slitP (hE : 0 < energy F u) (t : ℝ) : (qP u t, vP b F u hc t) ∈ slitDomain n :=
  tangent_mem_slitDomain (qP_unit u t) (vP_tangent b F u hc t) (vP_ne_zero b F u hc hE t)

/-- The force along the periodic jet. -/
def fP (A : Ambient n →L[ℝ] Ambient n) (t : ℝ) : ℝ := smoothForce F (qP u) (vP b F u hc) A t

theorem fP_continuous (hE : 0 < energy F u) (A : Ambient n →L[ℝ] Ambient n) :
    Continuous (fP b F u hc A) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hq : ContDiffAt ℝ (0 : ℕ) (qP u) t :=
    contDiffAt_zero.mpr ⟨univ, univ_mem, (qP_continuous u).continuousOn⟩
  have hv : ContDiffAt ℝ (0 : ℕ) (vP b F u hc) t :=
    contDiffAt_zero.mpr ⟨univ, univ_mem, (vP_continuous b F u hc).continuousOn⟩
  exact (smoothForce_contDiffAt_of_slit F A (slitP b F u hc hE t) hq hv).continuousAt

theorem fP_periodic (A : Ambient n →L[ℝ] Ambient n) : Function.Periodic (fP b F u hc A) 1 := by
  intro t
  have hq : qP u (t + 1) = qP u t := realMap_periodic u.data t
  have hv : vP b F u hc (t + 1) = vP b F u hc t := by
    unfold vP
    rw [Int.fract_add_one]
  unfold fP smoothForce
  rw [hq, hv]

theorem fP_eq_on (A : Ambient n →L[ℝ] Ambient n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fP b F u hc A t = smoothForce F qR vR A t := by
  have hq : qP u t = qR t := realMap_eqOn u.data ht
  unfold fP smoothForce
  rw [hq, vP_eq_on b F u hc ht]

/-- Rotational momenta extended to ℝ by integrating the periodic force. -/
def PA {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A) (t : ℝ) : ℝ :=
  momentumRepresentative F u hA hc 0 + ∫ x in (0 : ℝ)..t, fP b F u hc A x

theorem PA_hasDerivAt (hE : 0 < energy F u) {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) (t : ℝ) : HasDerivAt (PA b F u hc hA) (fP b F u hc A t) t :=
  ((fP_continuous b F u hc hE _).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

theorem PA_eq_on {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : PA b F u hc hA t = momentumRepresentative F u hA hc t := by
  unfold PA
  have hcongr : (∫ x in (0 : ℝ)..t, fP b F u hc A x) =
      ∫ x in (0 : ℝ)..t, smoothForce F qR vR A x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ht.1] at hx
    exact fP_eq_on b F u hc _ ⟨hx.1, hx.2.trans ht.2⟩
  rw [hcongr, ← momentum_sub_smoothForce b F u hc hA
    (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ht]
  ring

theorem PA_periodic (hE : 0 < energy F u) {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) : Function.Periodic (PA b F u hc hA) 1 := by
  intro t
  have hint (a c : ℝ) : IntervalIntegrable (fP b F u hc A) volume a c :=
    (fP_continuous b F u hc hE _).intervalIntegrable a c
  have h01 : (∫ x in (0 : ℝ)..1, fP b F u hc A x) = 0 := by
    have h := PA_eq_on b F u hc hA (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
    unfold PA at h
    rw [momentumRepresentative_periodic_trace] at h
    linarith
  have hper := (fP_periodic b F u hc A).intervalIntegral_add_eq t 0
  rw [zero_add] at hper
  unfold PA
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + 1)), hper, h01,
    add_zero]

theorem PA_eq_fract (hE : 0 < energy F u) {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) (t : ℝ) :
    PA b F u hc hA t = momentumRepresentative F u hA hc (Int.fract t) := by
  have h := (PA_periodic b F u hc hE hA).sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one, Int.self_sub_floor] at h
  rw [← h]
  exact PA_eq_on b F u hc hA (fract_mem_Icc t)

/-- Plane momenta extended to ℝ. -/
def PP (i j : ι) (t : ℝ) : ℝ := PA b F u hc (planeRotation_isRotation (b i) (b j)) t

theorem PP_hasDerivAt (hE : 0 < energy F u) (i j : ι) (t : ℝ) :
    HasDerivAt (PP b F u hc i j) (fP b F u hc (planeRotation (b i) (b j)) t) t :=
  PA_hasDerivAt b F u hc hE _ t

theorem PP_eq_fract (hE : 0 < energy F u) (i j : ι) (t : ℝ) :
    PP b F u hc i j t =
      momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc (Int.fract t) :=
  PA_eq_fract b F u hc hE _ t

theorem assembled_eq (hE : 0 < energy F u) (t : ℝ) :
    assembledCovector b (qP u) (PP b F u hc) t = recoveredCovector b F u hc (Int.fract t) := by
  unfold assembledCovector recoveredCovector
  simp only [qP_eq_fract u t, PP_eq_fract b F u hc hE]

theorem legendreP (hE : 0 < energy F u) (t : ℝ) :
    legendreExt F (qP u t, vP b F u hc t) =
      (qP u t, covectorVectorL n (assembledCovector b (qP u) (PP b F u hc) t)) := by
  rw [assembled_eq b F u hc hE t, qP_eq_fract u t]
  exact legendreExt_path b F u hc (fract_mem_Icc t)

/-- The periodic jet data of a positive tangent-critical loop, on all of ℝ. -/
def jetData (hE : 0 < energy F u) : JetData b F univ where
  q := qP u
  v := vP b F u hc
  P := PP b F u hc
  hasDerivAt_q := fun t _ => qP_hasDerivAt b F u hc t
  continuousOn_v := (vP_continuous b F u hc).continuousOn
  hasDerivAt_P := fun i j t _ => PP_hasDerivAt b F u hc hE i j t
  unit := fun t _ => qP_unit u t
  tangent := fun t _ => vP_tangent b F u hc t
  nonzero := fun t _ => vP_ne_zero b F u hc hE t
  legendre := fun t _ => legendreP b F u hc hE t

include b hc in
theorem qP_contDiff (hE : 0 < energy F u) : ContDiff ℝ ∞ (qP u) :=
  contDiff_iff_contDiffAt.mpr fun t =>
    jet_q_contDiffAt (jetData b F u hc hE) isOpen_univ (mem_univ t)

end Periodic

/-- Basis-free: the periodic real representative of a positive-energy tangent-critical
actual H¹ sphere loop is C^∞ on all of ℝ, including the periodic endpoint. -/
theorem realMap_contDiff (F : ReversibleMetric n) (u : Finsler.IntervalSobolev.SphereLoop n)
    (hc : Finsler.SobolevCurveVariation.TangentCritical F u)
    (hE : 0 < Finsler.SobolevEnergy.energy F u) :
    ContDiff ℝ ∞ (Finsler.SobolevCircleRepresentative.realMap u.data) :=
  qP_contDiff (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) F u hc hE

/-! ### Readback as an ordinary smooth closed geodesic -/

section Readback

open MeasureTheory Finsler.IntervalSobolev Finsler.SobolevRotationalVariation
open Finsler.SobolevCurveVariation Finsler.SobolevEnergyDifferential Finsler.SobolevEnergy
open Finsler.SobolevVelocityContinuity Finsler.SobolevCircleRepresentative
open Finsler.Loops Finsler.Geodesics Finsler.EnergyConservation TauCeti.Manifold
open scoped Manifold

variable (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n) (u : SphereLoop n)
  (hc : TangentCritical F u)

local notation "qR" => continuousRepresentative (u.data : Space n)
local notation "vR" => velocityRep b F u hc

theorem momentumRepresentative_eq_on {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    momentumRepresentative F u hA hc t = velocityDifferential F (qR t, vR t) (A (qR t)) := by
  have hae : momentumRepresentative F u hA hc =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun s => velocityDifferential F (qR s, vR s) (A (qR s)) := by
    have h1 := (momentum_ae_representative F u hA hc).symm
    have h2 := velocityRep_ae b F u hc
    change ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at h1 h2
    rw [restrict_Ioo_eq_restrict_Icc] at h1 h2
    filter_upwards [h1, h2] with s hs1 hs2
    rw [hs1, hs2]
    rfl
  have hcontR : ContinuousOn (fun s => velocityDifferential F (qR s, vR s) (A (qR s)))
      (Icc 0 1) := by
    intro s hs
    have hq := continuousRepresentative_continuousOn (u.data : Space n) s hs
    have hv : ContinuousWithinAt vR (Icc 0 1) s :=
      (velocityRep_continuous b F u hc).continuousAt.continuousWithinAt
    have hz : (qR s, vR s).1 ≠ 0 := by
      intro h
      have h1 := u.sphere_constraint ⟨s, hs⟩
      change ‖qR s‖ = 1 at h1
      rw [show qR s = 0 from h, norm_zero] at h1
      norm_num at h1
    have hvd : ContinuousWithinAt (fun x => velocityDifferential F (qR x, vR x)) (Icc 0 1) s :=
      ContinuousAt.comp_continuousWithinAt (g := velocityDifferential F)
        (f := fun x => (qR x, vR x)) (velocityDifferential_continuousAt F hz) (hq.prodMk hv)
    have hAq : ContinuousWithinAt (fun x => A (qR x)) (Icc 0 1) s :=
      ContinuousAt.comp_continuousWithinAt (g := A) (f := qR) A.continuous.continuousAt hq
    exact hvd.clm_apply hAq
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae
    (momentumRepresentative_continuousOn F u hA hc) hcontR ht

theorem PA_eq_jet (hE : 0 < energy F u) {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) (t : ℝ) :
    PA b F u hc hA t = velocityDifferential F (qP u t, vP b F u hc t) (A (qP u t)) := by
  rw [PA_eq_fract b F u hc hE hA t, momentumRepresentative_eq_on b F u hc hA (fract_mem_Icc t),
    qP_eq_fract u t]
  rfl

theorem qP_mem_sphere (t : ℝ) : qP u t ∈ Metric.sphere (0 : Ambient n) 1 := by
  simpa using qP_unit u t

/-- The smooth periodic loop obtained from a positive tangent-critical H¹ loop. -/
def geodesicLoop (hE : 0 < energy F u) : SmoothLoop n where
  curve := Set.codRestrict (qP u) (Metric.sphere (0 : Ambient n) 1) (qP_mem_sphere u)
  smooth := (contMDiff_iff_contDiff.mpr (qP_contDiff b F u hc hE)).codRestrict_sphere
    (qP_mem_sphere u)
  periodic := fun t => Subtype.ext (realMap_periodic u.data t)

theorem geodesicLoop_position (hE : 0 < energy F u) (t : ℝ) :
    position (geodesicLoop b F u hc hE) t = qP u t := rfl

theorem geodesicLoop_velocity (hE : 0 < energy F u) (t : ℝ) :
    velocity (geodesicLoop b F u hc hE) t = vP b F u hc t := by
  rw [velocity_eq_deriv]
  exact (qP_hasDerivAt b F u hc t).deriv

theorem geodesicLoop_jet (hE : 0 < energy F u) (t : ℝ) :
    loopJet (geodesicLoop b F u hc hE) t = (qP u t, vP b F u hc t) := by
  rw [loopJet_eq, geodesicLoop_position, geodesicLoop_velocity]

theorem geodesicLoop_regular (hE : 0 < energy F u) : Regular (geodesicLoop b F u hc hE) := by
  intro t h0
  have hv : Finsler.EnergyConservation.velocity (geodesicLoop b F u hc hE) t = 0 := by
    have h : Finsler.EnergyConservation.velocity (geodesicLoop b F u hc hE) t =
        ambientMap ((geodesicLoop b F u hc hE) t)
          (curveVelocity (𝓡 n) (geodesicLoop b F u hc hE) t) := by
      have hp := curveVelocityLift_proj (I := 𝓡 n) (geodesicLoop b F u hc hE).curve t
      simp only [Finsler.EnergyConservation.velocity, loopJet, Finsler.SphereRetraction.ambientPair,
        ambientVector, Finsler.LoopEnergy.velocityLift, curveVelocityLift_snd]
      exact congrArg (fun x : Sphere n =>
        ambientMap x (curveVelocity (𝓡 n) (geodesicLoop b F u hc hE).curve t)) hp
    rw [h, h0, map_zero]
  rw [geodesicLoop_velocity] at hv
  exact vP_ne_zero b F u hc hE t hv

theorem geodesicLoop_constrainedEuler (hE : 0 < energy F u) :
    Finsler.PointwiseEuler.ConstrainedEuler F (geodesicLoop b F u hc hE) := by
  intro t w hw
  have hreg := geodesicLoop_regular b F u hc hE
  have hq : ‖qP u t‖ = 1 := qP_unit u t
  have hw' : ⟪qP u t, w⟫ = 0 := hw
  have hA : InfinitesimalRotation (planeRotation w (qP u t)) :=
    planeRotation_isRotation w (qP u t)
  have hAq : planeRotation w (qP u t) (qP u t) = w := by
    rw [planeRotation_apply, real_inner_self_eq_norm_sq, hq, one_pow, one_smul,
      real_inner_comm, hw', zero_smul, sub_zero]
  have hjet := geodesicLoop_jet b F u hc hE
  have hmomeq : (fun s => Finsler.WeakEulerLagrange.momentum F (geodesicLoop b F u hc hE) s
      (planeRotation w (qP u t) (qP u s))) = PA b F u hc hA := by
    funext s
    rw [PA_eq_jet b F u hc hE hA s]
    simp only [Finsler.WeakEulerLagrange.momentum, hjet s]
  have hmom_diff : DifferentiableAt ℝ
      (Finsler.WeakEulerLagrange.momentum F (geodesicLoop b F u hc hE)) t :=
    (Finsler.WeakEulerLagrange.momentum_smooth F hreg).differentiable (by simp) t
  have hAq_deriv : HasDerivAt (fun s => planeRotation w (qP u t) (qP u s))
      (planeRotation w (qP u t) (vP b F u hc t)) t :=
    (planeRotation w (qP u t)).hasFDerivAt.comp_hasDerivAt t (qP_hasDerivAt b F u hc t)
  have h1 := hmom_diff.hasDerivAt.clm_apply hAq_deriv
  rw [hmomeq] at h1
  have huniq := h1.unique (PA_hasDerivAt b F u hc hE hA t)
  have hf : fP b F u hc (planeRotation w (qP u t)) t =
      positionDifferential F (qP u t, vP b F u hc t) (planeRotation w (qP u t) (qP u t)) +
        velocityDifferential F (qP u t, vP b F u hc t)
          (planeRotation w (qP u t) (vP b F u hc t)) := by
    unfold fP smoothForce
    rw [differential_split]
  have hmt : Finsler.WeakEulerLagrange.momentum F (geodesicLoop b F u hc hE) t =
      velocityDifferential F (qP u t, vP b F u hc t) := by
    simp only [Finsler.WeakEulerLagrange.momentum, hjet t]
  have hpt : Finsler.WeakEulerLagrange.positionTerm F (geodesicLoop b F u hc hE) t =
      positionDifferential F (qP u t, vP b F u hc t) := by
    simp only [Finsler.WeakEulerLagrange.positionTerm, hjet t]
  rw [hf, hmt] at huniq
  unfold Finsler.WeakEulerLagrange.residual
  rw [← hAq, sub_apply, hpt]
  linarith

/-- A positive tangent-critical actual H¹ loop is an ordinary smooth closed geodesic. -/
def closedGeodesic (hE : 0 < energy F u) : ClosedGeodesic F :=
  ⟨geodesicLoop b F u hc hE, geodesicLoop_regular b F u hc hE,
    Finsler.GeneralVariation.constrainedEuler_stationary F (geodesicLoop_regular b F u hc hE)
      (geodesicLoop_constrainedEuler b F u hc hE)⟩

end Readback

/-- Basis-free readback: every positive-energy tangent-critical actual H¹ sphere loop is
represented by a smooth regular variational closed geodesic with the same real
representative. -/
theorem exists_closedGeodesic_of_tangentCritical (F : ReversibleMetric n)
    (u : Finsler.IntervalSobolev.SphereLoop n)
    (hc : Finsler.SobolevCurveVariation.TangentCritical F u)
    (hE : 0 < Finsler.SobolevEnergy.energy F u) :
    ∃ γ : Finsler.Geodesics.ClosedGeodesic F, ∀ t,
      ((γ.loop t : Sphere n) : Ambient n) = Finsler.SobolevCircleRepresentative.realMap u.data t :=
  ⟨closedGeodesic (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) F u hc hE, fun _ => rfl⟩

end

end Finsler.SobolevGeodesicReadback
