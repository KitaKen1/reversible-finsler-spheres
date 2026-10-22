module

public import Finsler.Geometry.AmbientPenalty
public import Finsler.Geometry.EnergyDiagonal
public import Finsler.Analysis.PseudoGradient
public import Finsler.Analysis.SphereFlow

/-! Descents of the penalized polygon energy on ambient polygons. The polygon energy with
normalized vertices is invariant under positive rescalings of the vertices, so it has at an
ambient polygon with nonzero vertices the regularity it has at the normalized polygon; the
penalty is smooth there. In the direction of a vertex the derivative of the penalized energy is
2 λ times the logarithm of the norm of the vertex; hence a critical point has unit vertices, and
it is a sphere polygon which is stationary along all curves of sphere polygons. A Lipschitz
field which vanishes at the polygons with a zero vertex has a global flow keeping the polygons
with nonzero vertices, and gives a descent for every function which does not increase along the
field. With a pseudo-gradient this gives, for an open set containing the stationary sphere
polygons of a band, a descent of the penalized energy whose time-one map decreases it strictly
at the points of the band outside the open set. No tangential projection is needed. -/

@[expose] public section

namespace Finsler.AmbientDescent

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PolygonDescent
open Finsler.PseudoGradient Finsler.SphereFlow Finsler.FlowLens Finsler.AmbientPenalty
open Set Filter
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-! ### Regularity -/

omit [NeZero N] in
/-- The polygon energy with normalized vertices is invariant under positive rescalings of the
vertices. -/
theorem polyEnergyN_smul (F : ReversibleMetric n) (c : ZMod N → ℝ) (hc : ∀ j, 0 < c j)
    (Q : ZMod N → Ambient n) : polyEnergyN F N (fun j => c j • Q j) = polyEnergyN F N Q := by
  rw [polyEnergyN_eq_normalize, polyEnergyN_eq_normalize]
  congr 1
  funext j
  by_cases h : Q j = 0
  · rw [h, smul_zero]
  · rw [normalize_smul h (hc j)]

/-- The polygon energy with normalized vertices has at a polygon with nonzero vertices the
regularity it has at the normalized polygon. -/
theorem polyEnergyN_contDiffAt (F : ReversibleMetric n) {k : WithTop ℕ∞} (Q : Om n N)
    (h : ContDiffAt ℝ k (polyEnergyN F N) (amb (normalizeP Q))) :
    ContDiffAt ℝ k (polyEnergyN F N) Q.1 := by
  have hS : ContDiff ℝ k (fun Q' : ZMod N → Ambient n => fun j => ‖Q.1 j‖⁻¹ • Q' j) :=
    contDiff_pi.mpr fun j => (contDiff_apply ℝ (Ambient n) j).const_smul _
  have hSQ : (fun j => ‖Q.1 j‖⁻¹ • Q.1 j) = amb (normalizeP Q) := by
    funext j
    exact (coe_normalize (Q.2 j)).symm
  have hcomp : ContDiffAt ℝ k
      ((polyEnergyN F N) ∘ fun Q' : ZMod N → Ambient n => fun j => ‖Q.1 j‖⁻¹ • Q' j) Q.1 := by
    refine ContDiffAt.comp Q.1 ?_ hS.contDiffAt
    rw [hSQ]
    exact h
  have heq : ((polyEnergyN F N) ∘ fun Q' : ZMod N → Ambient n => fun j => ‖Q.1 j‖⁻¹ • Q' j) =
      polyEnergyN F N := by
    funext Q'
    exact polyEnergyN_smul F (fun j => ‖Q.1 j‖⁻¹)
      (fun j => inv_pos.mpr (norm_pos_iff.mpr (Q.2 j))) Q'
  rwa [heq] at hcomp

/-- The penalty is smooth at the polygons with nonzero vertices. -/
theorem logPen_contDiffAt (Q : Om n N) : ContDiffAt ℝ ∞ (logPen (n := n) (N := N)) Q.1 := by
  unfold logPen
  refine ContDiffAt.sum fun j _ => ContDiffAt.pow ?_ 2
  have h1 : ContDiffAt ℝ ∞ (fun Q' : ZMod N → Ambient n => ‖Q' j‖) Q.1 :=
    (contDiffAt_norm ℝ (Q.2 j)).comp Q.1 (contDiff_apply ℝ (Ambient n) j).contDiffAt
  exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr (Q.2 j))).comp Q.1 h1

/-- The penalized energy is C¹ at a polygon with nonzero vertices if the polygon energy with
normalized vertices is. -/
theorem pen_contDiffAt_one (F : ReversibleMetric n) (lam : ℝ) (Q : Om n N)
    (h : ContDiffAt ℝ 1 (polyEnergyN F N) Q.1) : ContDiffAt ℝ 1 (pen F N lam) Q.1 := by
  unfold pen
  exact h.add (contDiffAt_const.mul ((logPen_contDiffAt Q).of_le (by simp)))

/-! ### Critical points -/

/-- The penalty along the scaling of one vertex. -/
theorem hasDerivAt_logPen_radial (Q : Om n N) (j : ZMod N) :
    HasDerivAt (fun s : ℝ => logPen (Q.1 + s • (Pi.single j (Q.1 j) : ZMod N → Ambient n)))
      (2 * Real.log ‖Q.1 j‖) 0 := by
  have hr : 0 < ‖Q.1 j‖ := norm_pos_iff.mpr (Q.2 j)
  have hk : HasDerivAt (fun s : ℝ => Real.log ((1 + s) * ‖Q.1 j‖)) 1 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (1 + s) * ‖Q.1 j‖) ‖Q.1 j‖ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖Q.1 j‖
    have h2 := (Real.hasDerivAt_log (by simpa using hr.ne' : (1 + (0 : ℝ)) * ‖Q.1 j‖ ≠ 0)).comp
      (0 : ℝ) h1
    have h3 : ((1 + (0 : ℝ)) * ‖Q.1 j‖)⁻¹ * ‖Q.1 j‖ = 1 := by
      rw [add_zero, one_mul, inv_mul_cancel₀ hr.ne']
    rw [h3] at h2
    exact h2
  have hmodel : HasDerivAt (fun s : ℝ => Real.log ((1 + s) * ‖Q.1 j‖) ^ 2 +
      (logPen Q.1 - Real.log ‖Q.1 j‖ ^ 2)) (2 * Real.log ‖Q.1 j‖) 0 := by
    have h4 := (hk.pow 2).add_const (logPen Q.1 - Real.log ‖Q.1 j‖ ^ 2)
    simpa using h4
  refine hmodel.congr_of_eventuallyEq ?_
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < 1 + s := by
    have hc : Continuous fun s : ℝ => 1 + s := continuous_const.add continuous_id
    have h := hc.tendsto 0
    rw [add_zero] at h
    exact h.eventually (lt_mem_nhds zero_lt_one)
  filter_upwards [hpos] with s hs
  have hj : (Q.1 + s • (Pi.single j (Q.1 j) : ZMod N → Ambient n)) j = (1 + s) • Q.1 j := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, add_smul, one_smul]
  have hi : ∀ i, i ≠ j →
      (Q.1 + s • (Pi.single j (Q.1 j) : ZMod N → Ambient n)) i = Q.1 i := by
    intro i hij
    rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero, add_zero]
  unfold logPen
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase Finset.univ (fun i => Real.log ‖Q.1 i‖ ^ 2) (Finset.mem_univ j)]
  have hsum : ∑ i ∈ Finset.univ.erase j,
      Real.log ‖(Q.1 + s • (Pi.single j (Q.1 j) : ZMod N → Ambient n)) i‖ ^ 2 =
      ∑ i ∈ Finset.univ.erase j, Real.log ‖Q.1 i‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi' => by rw [hi i (Finset.ne_of_mem_erase hi')]
  rw [hsum, hj, norm_smul, Real.norm_of_nonneg hs.le]
  ring

/-- The derivative of the penalty in the direction of a vertex. -/
theorem fderiv_logPen_radial (Q : Om n N) (j : ZMod N) :
    fderiv ℝ (logPen (n := n) (N := N)) Q.1 (Pi.single j (Q.1 j)) = 2 * Real.log ‖Q.1 j‖ := by
  have hd : DifferentiableAt ℝ (logPen (n := n) (N := N)) Q.1 :=
    (logPen_contDiffAt Q).differentiableAt (by simp)
  have hc : HasDerivAt (fun s : ℝ => Q.1 + s • (Pi.single j (Q.1 j) : ZMod N → Ambient n))
      (Pi.single j (Q.1 j)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single j (Q.1 j) : ZMod N → Ambient n)).const_add Q.1
    rwa [one_smul] at h
  have hfd : HasFDerivAt (logPen (n := n) (N := N)) (fderiv ℝ logPen Q.1)
      (Q.1 + (0 : ℝ) • (Pi.single j (Q.1 j) : ZMod N → Ambient n)) := by
    rw [zero_smul, add_zero]
    exact hd.hasFDerivAt
  have h1 : HasDerivAt
      (fun s : ℝ => logPen (Q.1 + s • (Pi.single j (Q.1 j) : ZMod N → Ambient n)))
      (fderiv ℝ (logPen (n := n) (N := N)) Q.1 (Pi.single j (Q.1 j))) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (l := logPen (n := n) (N := N))
      (f := fun s : ℝ => Q.1 + s • (Pi.single j (Q.1 j) : ZMod N → Ambient n)) hfd hc
  exact h1.unique (hasDerivAt_logPen_radial Q j)

/-- A critical point of the penalized energy has unit vertices. -/
theorem norm_eq_one_of_critical (F : ReversibleMetric n) {lam : ℝ} (hlam : lam ≠ 0) (Q : Om n N)
    (hE : DifferentiableAt ℝ (polyEnergyN F N) Q.1) (h0 : fderiv ℝ (pen F N lam) Q.1 = 0)
    (j : ZMod N) : ‖Q.1 j‖ = 1 := by
  have hd : DifferentiableAt ℝ (logPen (n := n) (N := N)) Q.1 :=
    (logPen_contDiffAt Q).differentiableAt (by simp)
  have hsplit : fderiv ℝ (pen F N lam) Q.1 =
      fderiv ℝ (polyEnergyN F N) Q.1 + lam • fderiv ℝ (logPen (n := n) (N := N)) Q.1 := by
    have h := (hE.hasFDerivAt.add (hd.hasFDerivAt.const_mul lam)).fderiv
    exact h
  have hrad : fderiv ℝ (polyEnergyN F N) Q.1 (Pi.single j (Q.1 j)) = 0 :=
    fderiv_single_eq_zero hE (polyEnergyN_rescale F N Q.1 Q.2 j)
  have h1 : fderiv ℝ (pen F N lam) Q.1 (Pi.single j (Q.1 j)) = lam * (2 * Real.log ‖Q.1 j‖) := by
    rw [hsplit, add_apply, hrad, zero_add, smul_apply, fderiv_logPen_radial, smul_eq_mul]
  rw [h0, zero_apply] at h1
  have h2 : Real.log ‖Q.1 j‖ = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hlam
    · linarith
  exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (Q.2 j)) h2

/-- The penalty has derivative zero at the polygons with unit vertices. -/
theorem hasFDerivAt_logPen_unit (Q : Om n N) (hQ : ∀ j, ‖Q.1 j‖ = 1) :
    HasFDerivAt (logPen (n := n) (N := N)) (0 : (ZMod N → Ambient n) →L[ℝ] ℝ) Q.1 := by
  unfold logPen
  have hterm : ∀ j ∈ (Finset.univ : Finset (ZMod N)),
      HasFDerivAt (fun Q' : ZMod N → Ambient n => Real.log ‖Q' j‖ ^ 2)
        (0 : (ZMod N → Ambient n) →L[ℝ] ℝ) Q.1 := by
    intro j _
    have h1 : ContDiffAt ℝ ∞ (fun Q' : ZMod N → Ambient n => Real.log ‖Q' j‖) Q.1 :=
      (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr (Q.2 j))).comp Q.1
        ((contDiffAt_norm ℝ (Q.2 j)).comp Q.1 (contDiff_apply ℝ (Ambient n) j).contDiffAt)
    have h2 := (h1.differentiableAt (by simp)).hasFDerivAt.pow 2
    have h3 : Real.log ‖Q.1 j‖ = 0 := by rw [hQ j, Real.log_one]
    simp only [h3] at h2
    simpa using h2
  have hsum := HasFDerivAt.fun_sum hterm
  simpa using hsum

/-- A critical point of the penalized energy is a sphere polygon which is stationary along all
curves of sphere polygons. -/
theorem polyCritical_of_critical (F : ReversibleMetric n) {lam : ℝ} (hlam : lam ≠ 0) (Q : Om n N)
    (hE : DifferentiableAt ℝ (polyEnergyN F N) Q.1) (h0 : fderiv ℝ (pen F N lam) Q.1 = 0) :
    Q = incl (normalizeP Q) ∧ PolyCritical F N (normalizeP Q) := by
  have hunit := norm_eq_one_of_critical F hlam Q hE h0
  have hQ : Q.1 = amb (normalizeP Q) := by
    funext j
    change Q.1 j = (normalize (Q.1 j) : Ambient n)
    rw [coe_normalize (Q.2 j), hunit j, inv_one, one_smul]
  have hlog := hasFDerivAt_logPen_unit Q hunit
  have hpen : HasFDerivAt (pen F N lam) (fderiv ℝ (polyEnergyN F N) Q.1 +
      lam • (0 : (ZMod N → Ambient n) →L[ℝ] ℝ)) Q.1 :=
    hE.hasFDerivAt.add (hlog.const_mul lam)
  have hz : fderiv ℝ (polyEnergyN F N) Q.1 = 0 := by
    have h := hpen.fderiv
    rw [h0, smul_zero, add_zero] at h
    exact h.symm
  have hE0 : HasFDerivAt (polyEnergyN F N) (0 : (ZMod N → Ambient n) →L[ℝ] ℝ)
      (fun i => ((normalizeP Q) i : Ambient n)) := by
    have h := hE.hasFDerivAt
    rw [hz, hQ] at h
    exact h
  exact ⟨Subtype.ext hQ, polyCritical_of_hasFDerivAt F hE0⟩

/-! ### Flows keeping the polygons with nonzero vertices -/

section Flow

variable {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {K : ℝ≥0} (hL : LipschitzWith K V)
  (hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)

include hV0 in
theorem flow_ne_zero (Q : Om n N) (t : ℝ) (j : ZMod N) :
    ODE.globalSolution V hL Q.1 t j ≠ 0 := by
  by_cases h : V Q.1 = 0
  · rw [globalSolution_of_zero hL h]
    exact Q.2 j
  · exact hV0 _ (ne_zero_along hL h t) j

/-- The flow of the field at the time max(t, 0) on the polygons with nonzero vertices. -/
def flowOm (t : ℝ) (Q : Om n N) : Om n N :=
  ⟨ODE.globalSolution V hL Q.1 (max t 0), fun j => flow_ne_zero hL hV0 Q _ j⟩

theorem flowOm_continuous : Continuous fun p : ℝ × Om n N => flowOm hL hV0 p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  have h := ODE.continuous_globalSolution V hL
  have hpair : Continuous fun p : ℝ × Om n N => (max p.1 0, p.2.1) :=
    (continuous_fst.max continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)
  exact h.comp hpair

theorem flowOm_zero (Q : Om n N) : flowOm hL hV0 0 Q = Q := by
  apply Subtype.ext
  change ODE.globalSolution V hL Q.1 (max 0 0) = Q.1
  rw [max_self, ODE.globalSolution_zero]

theorem flowOm_add (s t : ℝ) (Q : Om n N) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    flowOm hL hV0 (s + t) Q = flowOm hL hV0 s (flowOm hL hV0 t Q) := by
  apply Subtype.ext
  change ODE.globalSolution V hL Q.1 (max (s + t) 0) =
    ODE.globalSolution V hL (ODE.globalSolution V hL Q.1 (max t 0)) (max s 0)
  rw [max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht, add_comm s t,
    ODE.globalSolution_add]

/-- The descent of a function which does not increase along the field. -/
def descentOf {g : (ZMod N → Ambient n) → ℝ} {O : Set (ZMod N → Ambient n)}
    (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
    (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0) : Descent (Om n N) (fun Q => g Q.1) where
  flow := flowOm hL hV0
  cont := flowOm_continuous hL hV0
  zero := flowOm_zero hL hV0
  add := flowOm_add hL hV0
  mono := fun t Q ht => by
    have hanti := antitoneOn_along hL hg hsupp (Q := Q.1) (T := t) (fun s _ hs => hle _ hs)
    have h := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    have h' : g (ODE.globalSolution V hL Q.1 t) ≤ g (ODE.globalSolution V hL Q.1 0) := h
    rw [ODE.globalSolution_zero] at h'
    change g (ODE.globalSolution V hL Q.1 (max t 0)) ≤ g Q.1
    rwa [max_eq_left ht]

/-- The time-one map of the descent decreases the function strictly at a point where the
derivative in the direction of the field is negative. -/
theorem descentOf_lt {g : (ZMod N → Ambient n) → ℝ} {O : Set (ZMod N → Ambient n)}
    (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
    (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0) (Q : Om n N) (hneg : fderiv ℝ g Q.1 (V Q.1) < 0) :
    g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1 := by
  change g (ODE.globalSolution V hL Q.1 (max 1 0)) < g Q.1
  rw [max_eq_left zero_le_one]
  exact lt_along hL hg hsupp zero_lt_one (fun s _ hs => hle _ hs) hneg

end Flow

/-! ### A descent of the penalized energy -/

/-- A descent of the penalized energy whose time-one map decreases it strictly at the points of
a band outside an open set containing the stationary sphere polygons of the band. -/
theorem exists_descent (F : ReversibleMetric n) (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ → ShortPolygon δ q)
    {𝒲 : Set (Om n N)} (h𝒲 : IsOpen 𝒲)
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ PolygonDescent.energy F N q →
      PolygonDescent.energy F N q ≤ b₀ → PolyCritical F N q → incl q ∈ 𝒲) :
    ∃ D : Descent (Om n N) (penW F N lam), ∀ Q : Om n N, a₀ ≤ penW F N lam Q →
      penW F N lam Q ≤ b₀ → Q ∉ 𝒲 → penW F N lam (D.flow 1 Q) < penW F N lam Q := by
  set O : Set (ZMod N → Ambient n) :=
    {Q | (∀ j, Q j ≠ 0) ∧ ContDiffAt ℝ 1 (pen F N lam) Q} with hOdef
  have hO : IsOpen O := by
    have h1 : IsOpen {Q : ZMod N → Ambient n | ∀ j, Q j ≠ 0} := by
      have he : {Q : ZMod N → Ambient n | ∀ j, Q j ≠ 0} =
          ⋂ j, (fun Q : ZMod N → Ambient n => Q j) ⁻¹' {y | y ≠ 0} := by
        ext Q
        simp
      rw [he]
      exact isOpen_iInter_of_finite fun j => isOpen_ne.preimage (continuous_apply j)
    have h2 : IsOpen {Q : ZMod N → Ambient n | ContDiffAt ℝ 1 (pen F N lam) Q} := by
      rw [isOpen_iff_mem_nhds]
      intro Q hQ
      exact ContDiffAt.eventually (show ContDiffAt ℝ 1 (pen F N lam) Q from hQ) (by simp)
    exact h1.inter h2
  have hfO : ContDiffOn ℝ 1 (pen F N lam) O := fun Q hQ => hQ.2.contDiffWithinAt
  have hdiff : ∀ P ∈ O, DifferentiableAt ℝ (pen F N lam) P := fun P hP =>
    hP.2.differentiableAt one_ne_zero
  have hcont := penW_continuous F hn (N := N) lam
  set C : Set (Om n N) := {Q | a₀ ≤ penW F N lam Q ∧ penW F N lam Q ≤ b₀} ∩ 𝒲ᶜ with hCdef
  have hCc : IsCompact C :=
    (band_isCompact F hn hlam a₀ b₀).inter_right h𝒲.isClosed_compl
  have hA : IsCompact (Subtype.val '' C) := hCc.image continuous_subtype_val
  -- regularity on the band
  have hEreg : ∀ Q : Om n N, penW F N lam Q ≤ b₀ → ContDiffAt ℝ 1 (polyEnergyN F N) Q.1 := by
    intro Q hQ
    have hle : PolygonDescent.energy F N (normalizeP Q) ≤ b₀ :=
      (energy_le_penW F hlam.le Q).trans hQ
    exact polyEnergyN_contDiffAt F Q (polyEnergyN_contDiffAt_one F hδ (hshort _ hle))
  have hAO : Subtype.val '' C ⊆ O := by
    rintro _ ⟨Q, hQ, rfl⟩
    exact ⟨Q.2, pen_contDiffAt_one F lam Q (hEreg Q hQ.1.2)⟩
  have hne : ∀ P ∈ Subtype.val '' C, fderiv ℝ (pen F N lam) P ≠ 0 := by
    rintro _ ⟨Q, hQ, rfl⟩ h0
    have hE := (hEreg Q hQ.1.2).differentiableAt one_ne_zero
    obtain ⟨hQeq, hpc⟩ := polyCritical_of_critical F hlam.ne' Q hE h0
    have hen : penW F N lam Q = PolygonDescent.energy F N (normalizeP Q) := by
      conv_lhs => rw [hQeq]
      exact penW_incl F lam _
    apply hQ.2
    rw [hQeq]
    exact hcrit _ (hen ▸ hQ.1.1) (hen ▸ hQ.1.2) hpc
  obtain ⟨V, hVs, hVcs, hVt, hVle, hVlt⟩ := exists_pseudoGradient hO hfO hA hAO hne
  obtain ⟨K, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVcs hVs (by simp)
  have hsupp : ∀ P, V P ≠ 0 → P ∈ O := fun P hP => hVt (subset_tsupport V hP)
  have hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0 := fun P hP => (hsupp P hP).1
  refine ⟨descentOf hL hV0 hdiff hsupp hVle, ?_⟩
  intro Q ha hb hQ
  exact descentOf_lt hL hV0 hdiff hsupp hVle Q (hVlt _ ⟨Q, ⟨⟨ha, hb⟩, hQ⟩, rfl⟩)

end

end Finsler.AmbientDescent
