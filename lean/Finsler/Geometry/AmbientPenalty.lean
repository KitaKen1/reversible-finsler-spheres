module

public import Finsler.Geometry.PolygonDescent
public import Finsler.Topology.LensFamily

/-! The penalized polygon energy on ambient polygons. On the open set of the polygons with N
nonzero vertices in the ambient space the polygon energy with normalized vertices is invariant
under positive rescalings of the vertices; adding λ times the sum of the squares of the
logarithms of the norms of the vertices gives a function whose bands are compact (λ > 0) and
whose sublevel pairs have the cohomology of the sublevel pairs of the polygon energy on the
space of sphere polygons: normalization maps the sublevels onto those of the polygon energy,
the inclusion of the sphere polygons is a section, and raising the norms of the vertices to the
power s, 0 ≤ s ≤ 1, is a homotopy from the normalization to the identity which does not increase
the penalized energy. This space is an open subset of a vector space, so descents can be
obtained from vector fields without constraints, and the cyclic rotation of the vertices acts
linearly. -/

@[expose] public section

namespace Finsler.AmbientPenalty

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.PolygonDescent Finsler.FlowLens Finsler.PairTriple
open Finsler.BorelCochain Finsler.BorelLoop Finsler.LensFamily Finsler.SphereDistance
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- The space of the ambient polygons with N nonzero vertices. -/
abbrev Om (n N : ℕ) : TopCat.{0} := TopCat.of {Q : ZMod N → Ambient n // ∀ j, Q j ≠ 0}

variable {N : ℕ} [NeZero N]

/-- The penalty: the sum of the squares of the logarithms of the norms of the vertices. -/
def logPen (Q : ZMod N → Ambient n) : ℝ := ∑ j, Real.log ‖Q j‖ ^ 2

theorem logPen_nonneg (Q : ZMod N → Ambient n) : 0 ≤ logPen Q :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The penalized polygon energy of an ambient polygon. -/
def pen (F : ReversibleMetric n) (N : ℕ) [NeZero N] (lam : ℝ) (Q : ZMod N → Ambient n) : ℝ :=
  polyEnergyN F N Q + lam * logPen Q

omit [NeZero N] in
/-- The polygon energy with normalized vertices is the polygon energy of the normalized
polygon. -/
theorem polyEnergyN_eq_normalize (F : ReversibleMetric n) (Q : ZMod N → Ambient n) :
    polyEnergyN F N Q = polyEnergy F N (fun j => (normalize (Q j) : Ambient n)) := rfl

omit [NeZero N] in
theorem polyEnergyN_nonneg (F : ReversibleMetric n) (Q : ZMod N → Ambient n) :
    0 ≤ polyEnergyN F N Q := by
  rw [polyEnergyN_eq_normalize]
  unfold polyEnergy
  exact mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun k _ => minEnergy_nonneg F _ _)

theorem coe_normalize {x : Ambient n} (hx : x ≠ 0) : (normalize x : Ambient n) = ‖x‖⁻¹ • x :=
  congrArg Subtype.val (normalize_coe (⟨x, hx⟩ : nonzeroAmbient n))

omit [NeZero N] in
/-- The normalization of a polygon with nonzero vertices. -/
def normalizeP : C(Om n N, Poly n N) :=
  ⟨fun Q j => normalize (Q.1 j), continuous_pi fun j => continuous_iff_continuousAt.mpr fun Q => by
    have h1 : ContinuousAt (fun Q : Om n N => Q.1 j) Q :=
      ((continuous_apply j).comp continuous_subtype_val).continuousAt
    have h2 : ContinuousAt (normalize (n := n)) (Q.1 j) :=
      (normalize_smoothAt (Q.2 j)).continuousAt
    exact ContinuousAt.comp (g := normalize) (f := fun Q : Om n N => Q.1 j) h2 h1⟩

omit [NeZero N] in
theorem energy_normalizeP (F : ReversibleMetric n) (Q : Om n N) :
    PolygonDescent.energy F N (normalizeP Q) = polyEnergyN F N Q.1 := rfl

omit [NeZero N] in
/-- The inclusion of the sphere polygons. -/
def incl : C(Poly n N, Om n N) :=
  ⟨fun q => ⟨amb q, fun j h => by
      have h1 := norm_amb q j
      rw [h, norm_zero] at h1
      exact zero_ne_one h1⟩,
    (amb_continuous N).subtype_mk _⟩

omit [NeZero N] in
theorem normalizeP_incl (q : Poly n N) : normalizeP (incl q) = q := by
  funext j
  exact normalize_inclusion (q j)

theorem logPen_incl (q : Poly n N) : logPen (incl q : Om n N).1 = 0 := by
  unfold logPen
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (incl q : Om n N).1 j = amb q j from rfl, norm_amb, Real.log_one]
  norm_num

/-- Raising the norms of the vertices to the power s. -/
def scal (s : ℝ) (Q : Om n N) : Om n N :=
  ⟨fun j => (‖Q.1 j‖ ^ (s - 1)) • Q.1 j, fun j =>
    smul_ne_zero (Real.rpow_pos_of_pos (norm_pos_iff.mpr (Q.2 j)) _).ne' (Q.2 j)⟩

omit [NeZero N] in
theorem norm_scal (s : ℝ) (Q : Om n N) (j : ZMod N) : ‖(scal s Q).1 j‖ = ‖Q.1 j‖ ^ s := by
  have hpos : 0 < ‖Q.1 j‖ := norm_pos_iff.mpr (Q.2 j)
  change ‖(‖Q.1 j‖ ^ (s - 1)) • Q.1 j‖ = _
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
  conv_rhs => rw [show s = (s - 1) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]

omit [NeZero N] in
theorem scal_continuous : Continuous fun p : ℝ × Om n N => scal p.1 p.2 := by
  refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
  have h0 : Continuous fun p : ℝ × Om n N => p.2.1 j :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  have h2 : Continuous fun p : ℝ × Om n N => ‖p.2.1 j‖ ^ (p.1 - 1) :=
    (continuous_norm.comp h0).rpow (continuous_fst.sub continuous_const)
      (fun p => Or.inl (norm_pos_iff.mpr (p.2.2 j)).ne')
  exact h2.smul h0

omit [NeZero N] in
theorem scal_one (Q : Om n N) : scal 1 Q = Q := by
  apply Subtype.ext
  funext j
  change (‖Q.1 j‖ ^ ((1 : ℝ) - 1)) • Q.1 j = Q.1 j
  rw [sub_self, Real.rpow_zero, one_smul]

omit [NeZero N] in
theorem scal_zero (Q : Om n N) : scal 0 Q = incl (normalizeP Q) := by
  apply Subtype.ext
  funext j
  change (‖Q.1 j‖ ^ ((0 : ℝ) - 1)) • Q.1 j = (normalize (Q.1 j) : Ambient n)
  rw [coe_normalize (Q.2 j), zero_sub, Real.rpow_neg_one]

omit [NeZero N] in
/-- The polygon energy with normalized vertices does not change under the scalings. -/
theorem polyEnergyN_scal (F : ReversibleMetric n) (s : ℝ) (Q : Om n N) :
    polyEnergyN F N (scal s Q).1 = polyEnergyN F N Q.1 := by
  rw [polyEnergyN_eq_normalize, polyEnergyN_eq_normalize]
  congr 1
  funext j
  rw [show (scal s Q).1 j = (‖Q.1 j‖ ^ (s - 1)) • Q.1 j from rfl,
    normalize_smul (Q.2 j) (Real.rpow_pos_of_pos (norm_pos_iff.mpr (Q.2 j)) _)]

theorem logPen_scal (s : ℝ) (Q : Om n N) : logPen (scal s Q).1 = s ^ 2 * logPen Q.1 := by
  unfold logPen
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_scal, Real.log_rpow (norm_pos_iff.mpr (Q.2 j))]
  ring

/-- The penalized polygon energy as a function on the space of ambient polygons with nonzero
vertices. -/
def penW (F : ReversibleMetric n) (N : ℕ) [NeZero N] (lam : ℝ) (Q : Om n N) : ℝ :=
  pen F N lam Q.1

/-- The scalings by powers between 0 and 1 do not increase the penalized energy. -/
theorem penW_scal_le (F : ReversibleMetric n) {lam : ℝ} (hlam : 0 ≤ lam) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (Q : Om n N) : penW F N lam (scal s Q) ≤ penW F N lam Q := by
  unfold penW pen
  rw [polyEnergyN_scal, logPen_scal]
  have h1 : s ^ 2 ≤ 1 := by nlinarith
  have h2 := logPen_nonneg Q.1
  nlinarith [mul_nonneg hlam (mul_nonneg (sub_nonneg.mpr h1) h2)]

theorem energy_le_penW (F : ReversibleMetric n) {lam : ℝ} (hlam : 0 ≤ lam) (Q : Om n N) :
    PolygonDescent.energy F N (normalizeP Q) ≤ penW F N lam Q := by
  rw [energy_normalizeP]
  unfold penW pen
  linarith [mul_nonneg hlam (logPen_nonneg Q.1)]

theorem penW_incl (F : ReversibleMetric n) (lam : ℝ) (q : Poly n N) :
    penW F N lam (incl q) = PolygonDescent.energy F N q := by
  unfold penW pen
  rw [logPen_incl, mul_zero, add_zero, energy_eq]
  rfl

theorem logPen_continuous : Continuous fun Q : Om n N => logPen Q.1 := by
  unfold logPen
  refine continuous_finsetSum _ fun j _ => Continuous.pow ?_ 2
  exact Real.continuousOn_log.comp_continuous
    (continuous_norm.comp ((continuous_apply j).comp continuous_subtype_val))
    (fun Q => (norm_pos_iff.mpr (Q.2 j)).ne')

theorem penW_continuous (F : ReversibleMetric n) (hn : 1 ≤ n) (lam : ℝ) :
    Continuous (penW F N lam) := by
  have h1 : Continuous fun Q : Om n N => PolygonDescent.energy F N (normalizeP Q) :=
    (PolygonDescent.energy_continuous F hn N).comp normalizeP.continuous
  have h2 : (fun Q : Om n N => PolygonDescent.energy F N (normalizeP Q)) =
      fun Q : Om n N => polyEnergyN F N Q.1 := funext fun Q => energy_normalizeP F Q
  rw [h2] at h1
  have h3 : penW F N lam = fun Q : Om n N => polyEnergyN F N Q.1 + lam * logPen Q.1 := rfl
  rw [h3]
  exact h1.add (continuous_const.mul logPen_continuous)

/-! ### The sublevel pairs -/

variable (F : ReversibleMetric n) {lam : ℝ}

/-- Normalization on a sublevel. -/
def normalizeMap (hlam : 0 ≤ lam) (b : ℝ) :
    C(sub (penW F N lam) b, sub (PolygonDescent.energy F N) b) :=
  ⟨fun Q => ⟨normalizeP Q.1, lt_of_le_of_lt (energy_le_penW F hlam Q.1) Q.2⟩,
    (normalizeP.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The inclusion of a sublevel of the polygon energy. -/
def inclMap (lam b : ℝ) : C(sub (PolygonDescent.energy F N) b, sub (penW F N lam) b) :=
  ⟨fun q => ⟨incl q.1, lt_of_eq_of_lt (penW_incl F lam q.1) q.2⟩,
    (incl.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem normalize_incl (hlam : 0 ≤ lam) (b : ℝ) :
    (normalizeMap F hlam b).comp (inclMap F lam b) =
      ContinuousMap.id (sub (PolygonDescent.energy F N) b) :=
  ContinuousMap.ext fun q => Subtype.ext (normalizeP_incl q.1)

/-- The scalings join the normalization to the identity of a sublevel. -/
def scalHomotopy (hlam : 0 ≤ lam) (b : ℝ) :
    ((inclMap F lam b).comp (normalizeMap F hlam b)).Homotopy
      (ContinuousMap.id (sub (penW F N lam) b)) where
  toFun p := ⟨scal (p.1 : ℝ) p.2.1,
    lt_of_le_of_lt (penW_scal_le F hlam p.1.2.1 p.1.2.2 p.2.1) p.2.2⟩
  continuous_toFun := (scal_continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left Q := Subtype.ext (by
    change scal ((0 : unitInterval) : ℝ) Q.1 = incl (normalizeP Q.1)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, scal_zero])
  map_one_left Q := Subtype.ext (by
    change scal ((1 : unitInterval) : ℝ) Q.1 = Q.1
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, scal_one])

/-- Normalization is bijective on the cohomology of the sublevel pairs: the sublevel pairs of
the penalized energy have the cohomology of those of the polygon energy. -/
theorem normalize_bijective (hlam : 0 ≤ lam) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX (sub_mono (penW F N lam) hab)
      (sub_mono (PolygonDescent.energy F N) hab) (normalizeMap F hlam b)
      (fun Q hQ => lt_of_le_of_lt (energy_le_penW F hlam Q.1) hQ))) k) := by
  refine bijective_Hmap_of_section _ _ (normalizeMap F hlam b) (inclMap F lam b) _ ?_
    (normalize_incl F hlam b) (scalHomotopy F hlam b) ?_ k
  · intro q hq
    exact lt_of_eq_of_lt (penW_incl F lam q.1) hq
  · intro τ Q hQ
    exact lt_of_le_of_lt (penW_scal_le F hlam τ.2.1 τ.2.2 Q.1) hQ

/-- The bands of the penalized energy are compact. -/
theorem band_isCompact (hn : 1 ≤ n) (hlam : 0 < lam) (a₀ b₀ : ℝ) :
    IsCompact {Q : Om n N | a₀ ≤ penW F N lam Q ∧ penW F N lam Q ≤ b₀} := by
  have hφ : Continuous fun p : Poly n N × (ZMod N → ℝ) =>
      (⟨fun j => Real.exp (p.2 j) • (p.1 j : Ambient n), fun j =>
        smul_ne_zero (Real.exp_pos _).ne' (fun h => by
          have h1 := norm_amb p.1 j
          rw [show amb p.1 j = (p.1 j : Ambient n) from rfl, h, norm_zero] at h1
          exact zero_ne_one h1)⟩ : Om n N) := by
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    exact (Real.continuous_exp.comp ((continuous_apply j).comp continuous_snd)).smul
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst))
  have hK : IsCompact ((univ : Set (Poly n N)) ×ˢ
      Metric.closedBall (0 : ZMod N → ℝ) (Real.sqrt (b₀ / lam))) :=
    isCompact_univ.prod (isCompact_closedBall 0 _)
  have hc := penW_continuous F hn (N := N) lam
  refine (hK.image hφ).of_isClosed_subset
    ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)) ?_
  rintro Q ⟨-, hb⟩
  refine ⟨(normalizeP Q, fun j => Real.log ‖Q.1 j‖), ⟨mem_univ _, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro j
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    have h1 : Real.log ‖Q.1 j‖ ^ 2 ≤ logPen Q.1 :=
      Finset.single_le_sum (f := fun j => Real.log ‖Q.1 j‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 : lam * logPen Q.1 ≤ b₀ := by
      have h3 : polyEnergyN F N Q.1 + lam * logPen Q.1 ≤ b₀ := hb
      linarith [polyEnergyN_nonneg F Q.1]
    rw [le_div_iff₀ hlam]
    nlinarith
  · apply Subtype.ext
    funext j
    have hpos : 0 < ‖Q.1 j‖ := norm_pos_iff.mpr (Q.2 j)
    change Real.exp (Real.log ‖Q.1 j‖) • (normalize (Q.1 j) : Ambient n) = Q.1 j
    rw [Real.exp_log hpos, coe_normalize (Q.2 j), smul_smul, mul_inv_cancel₀ hpos.ne',
      one_smul]

end

end Finsler.AmbientPenalty
