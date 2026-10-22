module

public import Finsler.Geometry.RoundLoopCross
public import Finsler.Geometry.RoundLevelCup
public import Finsler.Geometry.RoundFiltration

/-! The evaluation class on the round crossings of the loop space and the e-compatibility.

Sampling and normalization (`AmbientLoopPairs.nonempty_loop_equiv`) are maps of pairs over the
evaluation at 0 (vertex 0), so by `RoundLevelCup.round_level_cup` the cup with e = ev₀^*[Sⁿ]
annihilates no nonzero class of the round loop crossing (t_b, t_a) in the degree of the index, as
soon as the cup with π^*[Sⁿ] is injective on H⁰(V₂). Forgetting the reflection Borel structure
(`BorelCup.cup_forgetNative`), this is the e-compatibility `RoundFiltration.ECompat` of the round
crossings. -/

@[expose] public section

namespace Finsler.RoundLoopCup

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundChart Finsler.RoundThom Finsler.RoundLevel Finsler.AmbientPenalty
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.PolygonDescent Finsler.PolygonSampling
open Finsler.EnergyDiagonal Finsler.LoopCrossingOriented Finsler.AmbientLoopPairs
open Finsler.EnergySphereSmooth Finsler.LensFamily Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.BorelCrossing Module Set
open scoped Real

open SphereOddDegree Finsler.ECup Finsler.ECupThom Finsler.ECupTransport Finsler.RoundLevelCup
open Finsler.RoundFiltration Finsler.RoundCrossPattern Finsler.BorelGraded

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- Evaluation at 0 on the loop space. -/
def evL (n : ℕ) : Loops n ⟶ Finsler.BorelEvaluation.sphere n :=
  TopCat.ofHom (Finsler.BorelEvaluation.eval n)

/-- Evaluation at the vertex 0 of the polygons. -/
def evP (n N : ℕ) : PolygonDescent.Poly n N ⟶ Finsler.BorelEvaluation.sphere n :=
  TopCat.ofHom (ContinuousMap.eval 0)

theorem sampleTime_zero (N : ℕ) [NeZero N] :
    Finsler.PolygonCritical.sampleTime N 0 = Finsler.BorelEvaluation.zero :=
  Subtype.ext (by simp [Finsler.PolygonCritical.sampleTime, Finsler.BorelEvaluation.zero])

set_option maxHeartbeats 1600000 in
/-- **The evaluation class on the round crossings of the loop space.** -/
theorem round_loop_cup (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) {a b : ℝ}
    (hlo : 2 * π * ((m : ℝ) - 1) < a) (hac : a < 2 * π * m) (hcb : 2 * π * m < b)
    (hhi : b < 2 * π * ((m : ℝ) + 1))
    (hV : CupInjW (eV n hn) (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) 0)
    (hab : a ≤ b) :
    CupInjW ((cohPullback (evL n) n).hom (Finsler.SphereTopClass.topClass n hn))
      (lev_mono (roundMetric n) hab) ((2 * m - 1) * (n - 1)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hπ : 0 < π := Real.pi_pos
  have hlo0 : 0 ≤ 2 * π * ((m : ℝ) - 1) := by
    have : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
    positivity
  have ha : 0 < a := lt_of_le_of_lt hlo0 hlo
  -- segment data, polygon models and short polygons
  obtain ⟨S₀⟩ := exists_segmentData (roundMetric n)
  obtain ⟨δ₁, hδ₁, hC1⟩ := exists_ambientMinEnergy_contDiffAt_one (roundMetric n)
  set S := shrink S₀ (δ' := min S₀.δ (min δ₁ 2)) (lt_min S₀.pos (lt_min hδ₁ two_pos))
    (min_le_left _ _) with hS
  have hSδ : S.δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hSδ2 : S.δ ≤ 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing (roundMetric n) (δ := S.δ) (a := b) S.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound (roundMetric n) hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (b ^ 2 / (e * S.δ ^ 2))
  set M := N₁ + N₂ + m + 1 with hM
  set N := 2 * M + 1 with hN
  haveI : NeZero N := ⟨by omega⟩
  have hNpos : 0 < N := by omega
  let MK : PolygonModelData (roundMetric n) b N :=
    PolygonModelData.mk S fun u hu s' t hs' ht hst => hN₁ N (by omega) hNpos u hu s' t hs' ht hst
  have hKR : b ^ 2 / (e * S.δ ^ 2) < N := hN₂.trans_le (Nat.cast_le.mpr (by omega))
  have hshortK : ∀ q : ZMod N → Sphere n, PolygonDescent.energy (roundMetric n) N q ≤ b ^ 2 →
      ShortPolygon MK.δ q := fun q hq => short_of_energy_le he S.pos hedge hKR q hq
  have hCK : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < MK.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy (roundMetric n)) ((P : Ambient n), (Q : Ambient n)) :=
    fun P Q h => hC1 P Q (h.trans_le hSδ)
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  -- the crossing of the polygon level
  have hpoly := round_level_cup (N := N) hn (M := M) hN hm (by omega) hSδ2 hCK
    (a := a ^ 2) (b := b ^ 2) (by positivity) (pow_lt_pow_left₀ hlo hlo0 two_ne_zero)
    (pow_lt_pow_left₀ hac ha.le two_ne_zero)
    (pow_lt_pow_left₀ hcb (by positivity) two_ne_zero)
    (pow_lt_pow_left₀ hhi (ha.le.trans hab) two_ne_zero) hshortK hV hab2
  -- the ambient polygons and the polygons
  have hn1 := normalize_bijective (roundMetric n) (N := N) zero_le_one hab2 ((2 * m - 1) * (n - 1))
  have hn2 := normalize_bijective (roundMetric n) (N := N) zero_le_one hab2
    (n + (2 * m - 1) * (n - 1))
  have hP := (cupInjW_common (evOm n N) (evP n N) (Finsler.SphereTopClass.topClass n hn) _ rfl
    hn1 hn2).mpr hpoly
  -- the polygons and the loops
  have hs1 := Finsler.PolygonLoopPairs.sample_bijective MK (fun q hq => hshortK q hq.le) ha hab le_rfl
    ((2 * m - 1) * (n - 1))
  have hs2 := Finsler.PolygonLoopPairs.sample_bijective MK (fun q hq => hshortK q hq.le) ha hab le_rfl
    (n + (2 * m - 1) * (n - 1))
  refine (cupInjW_common (evL n) (evP n N) (Finsler.SphereTopClass.topClass n hn) _ ?_
    hs1 hs2).mp hP
  ext u : 1
  change Finsler.PolygonSampling.samplePoly N u.1 0 = Finsler.BorelEvaluation.eval n u.1
  change Finsler.IntervalSobolev.sphereRepresentative u.1
    (Finsler.PolygonCritical.sampleTime N 0) = _
  rw [sampleTime_zero]
  rfl

theorem forget_castHR_ne {K : InvComplex} {a b : ℕ} (h : a = b) (x : HR K a) :
    forget K b (castHR h x) ≠ 0 ↔ forget K a x ≠ 0 := by
  subst h
  rfl

/-- **The e-compatibility of the round crossings**, from the injectivity of the cup with
π^*[Sⁿ] on H⁰(V₂). -/
theorem ecompat_of (hn : 3 ≤ n)
    (hV : CupInjW (eV n (by omega)) (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ) 0) :
    ECompat n hn := by
  intro j τ hτ
  rw [forget_castHR_ne]
  have hC := round_loop_cup (by omega) (Nat.succ_pos j) (cut_lo j) (cut_ac j) (cut_cb j)
    (cut_hi j) hV (cut_mono j)
  set P := Finsler.BorelCrossing.crossPair (roundMetric n) (cut_mono j) with hP
  have ha : res ((cohPullback (evL n) n).hom (Finsler.SphereTopClass.topClass n (by omega)))
      (Finsler.BorelLoop.lev (roundMetric n) (cut (j + 1))) =
      (cohPullback (Finsler.BorelCrossing.crossEval (roundMetric n) (cut_mono j)) n).hom
        (Finsler.SphereTopClass.topClass n (by omega)) := by
    unfold res
    exact (Finsler.Cup.pullback_comp _ _ n _).symm
  -- the native forgotten class of τ
  set y := BorelComparison.forgetNative P (Finsler.BorelCrossing.revCross (roundMetric n) (cut_mono j))
    (Finsler.BorelCrossing.revCross_sq (roundMetric n) (cut_mono j)) (lc n (j + 1)) τ with hy
  have hy0 : y ≠ 0 := by
    intro h0
    apply hτ
    exact (BorelComparison.ordinaryEquiv P _ _ _).injective
      (h0.trans (BorelComparison.ordinaryEquiv P _ _ _).map_zero.symm)
  have hx0 : (BorelComparison.ordinaryEquiv P (𝟙 P) (Category.comp_id _) (lc n (j + 1))).symm y ≠ 0 :=
    fun h0 => hy0 (by rw [← LinearEquiv.apply_symm_apply
      (BorelComparison.ordinaryEquiv P (𝟙 P) (Category.comp_id _) (lc n (j + 1))) y, h0,
      LinearEquiv.map_zero])
  have hcup := hC _ hx0
  rw [ha] at hcup
  -- the cup in native cohomology
  have hrel : Finsler.RelativeCup.cup P n (lc n (j + 1))
      ((cohPullback (Finsler.BorelCrossing.crossEval (roundMetric n) (cut_mono j)) n).hom
        (Finsler.SphereTopClass.topClass n (by omega))) y ≠ 0 := by
    intro h0
    apply hcup
    change (BorelComparison.ordinaryEquiv P (𝟙 P) (Category.comp_id _) _).symm
      (Finsler.RelativeCup.cup P n (lc n (j + 1)) _
        (BorelComparison.ordinaryEquiv P (𝟙 P) (Category.comp_id _) _
          ((BorelComparison.ordinaryEquiv P (𝟙 P) (Category.comp_id _) _).symm y))) = 0
    rw [LinearEquiv.apply_symm_apply, h0, LinearEquiv.map_zero]
  -- the forgotten class of e·τ
  intro h0
  apply hrel
  have hf := BorelCup.cup_forgetNative P (Finsler.BorelCrossing.revCross (roundMetric n) (cut_mono j))
    (Finsler.BorelCrossing.revCross_sq (roundMetric n) (cut_mono j)) n
    (cochainPullback (Finsler.BorelCrossing.crossEval (roundMetric n) (cut_mono j)) n
      (classRepr (Finsler.BorelEvaluation.sphere n) n (Finsler.SphereTopClass.topClass n (by omega))))
    (cochainPullback_cocycle _ _ _ (classRepr_isCocycle (Finsler.BorelEvaluation.sphere n) n
      (Finsler.SphereTopClass.topClass n (by omega))))
    (Finsler.BorelEvaluation.cochain_invariant _ _
      (Finsler.BorelCrossing.crossEval_invariant (roundMetric n) (cut_mono j)) n _) (lc n (j + 1)) τ
  have hcls : CochainClass.classOf (cochainCxZMod2 P.fst) n
      (cochainPullback (Finsler.BorelCrossing.crossEval (roundMetric n) (cut_mono j)) n
        (classRepr (Finsler.BorelEvaluation.sphere n) n (Finsler.SphereTopClass.topClass n (by omega))))
      (cochainPullback_cocycle _ _ _ (classRepr_isCocycle (Finsler.BorelEvaluation.sphere n) n
        (Finsler.SphereTopClass.topClass n (by omega)))) =
      (cohPullback (Finsler.BorelCrossing.crossEval (roundMetric n) (cut_mono j)) n).hom
        (Finsler.SphereTopClass.topClass n (by omega)) := by
    have h1 := cohPullback_cocycleClass (Finsler.BorelCrossing.crossEval (roundMetric n) (cut_mono j)) n
      (classRepr (Finsler.BorelEvaluation.sphere n) n (Finsler.SphereTopClass.topClass n (by omega)))
      (classRepr_isCocycle (Finsler.BorelEvaluation.sphere n) n
        (Finsler.SphereTopClass.topClass n (by omega)))
    rw [cocycleClass_classRepr] at h1
    exact h1.symm
  rw [hcls] at hf
  rw [← hf]
  change BorelComparison.ordinaryEquiv P _ _ _ (forget _ _ (Finsler.BorelCrossing.crossE (roundMetric n)
    (cut_mono j) (by omega) (lc n (j + 1)) τ)) = 0
  rw [h0, LinearEquiv.map_zero]

end

end Finsler.RoundLoopCup
