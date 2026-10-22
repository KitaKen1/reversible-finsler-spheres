module

public import Finsler.Residual.FullHRAbs
public import Finsler.Loop.MeridianEquatorHomology

/-! The resonance bands HR of `BasisResidual.FillRes` with finitely many prime closed geodesics
(Claude, full-HR prototype).

The official ordinary class x of (Λ, M) restricts to zero on the energy sublevel t_a exactly when
its absolute singular class (`HRClasses.toAbs`) restricts to zero on t_a, in every degree above
n + 1 (`res_zero_iff`: naturality of the singular comparison and of the relative-to-absolute map,
injective there). Energy sublevels sit between length sublevels (`vanish_of_length`,
`ne_of_length`), so the length bands of `FullHRAbs.band` give `res_inj` and `res_zero` with the
rate α = 2m/β (`hr_of_finite`). -/

@[expose] public section

namespace Finsler.HRBridge

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.BorelCochain

noncomputable section
set_option autoImplicit false

variable (m : ℕ) (F : ReversibleMetric (m + 1))

/-- The inclusion of an energy sublevel into the loop space. -/
abbrev inclE (a : ℝ) : TopCat.of (lev F a) ⟶ Loops (m + 1) :=
  SupportedCap.subspaceMap (Loops (m + 1)) (lev F a)

/-- The absolute class on t_a of an ordinary class of (t_a, M). -/
def toAbsLev (a : ℝ) (i : ℕ) (y : H (levComplex F a) i) : cohomologyZMod2 (TopCat.of (lev F a)) i :=
  (relativeToPool (levPair F a) i).hom
    (Finsler.BorelComparison.ordinaryEquiv (levPair F a) (revPair F a) (revPair_sq F a) i y)

theorem toAbsLev_injective (a : ℝ) (i : ℕ) (hi : (m + 1) + 1 < i) :
    Function.Injective (toAbsLev m F a i) := by
  intro y y' h
  apply (Finsler.BorelComparison.ordinaryEquiv (levPair F a) (revPair F a) (revPair_sq F a) i).injective
  exact RelativeAbsoluteIso.injective (levPair F a) (i - 1) i (by omega)
    (ConstantLoopModel.cohomology_subsingleton (m + 1) (i - 1) (by omega) (by omega)) h

theorem toAbs_apply (i : ℕ) (hi : (m + 1) + 1 < i) (x : H (fullComplex (m + 1)) i) :
    HRClasses.toAbs (m + 1) i hi x = (cohPullback (FullLoopModel.insert (m + 1)) i).hom
      ((relativeToPool (fullPair (m + 1)) i).hom
        (Finsler.BorelComparison.ordinaryEquiv (fullPair (m + 1)) (revFullPair (m + 1))
          (revFullPair_sq (m + 1)) i x)) := rfl

theorem incl_insert (a : ℝ) :
    inclE m F a ≫ FullLoopModel.insert (m + 1) = TopPair.Hom.fst (resPair F a) := by
  ext u : 1
  rfl

/-- **The square**: restricting then comparing equals comparing then restricting. -/
theorem toAbsLev_res (a : ℝ) (i : ℕ) (hi : (m + 1) + 1 < i) (x : H (fullComplex (m + 1)) i) :
    toAbsLev m F a i (Hmap (resHom F a) i x) =
      (cohPullback (inclE m F a) i).hom (HRClasses.toAbs (m + 1) i hi x) := by
  rw [toAbsLev, Finsler.BorelComparison.ordinaryEquiv_natural (revPair_sq F a) (revFullPair_sq (m + 1))
    (resPair F a) (resPair_equivariant F a) i x, toAbs_apply]
  have hn := ConcreteCategory.congr_hom (relative_to_absolute_natural (resPair F a) i)
    (Finsler.BorelComparison.ordinaryEquiv (fullPair (m + 1)) (revFullPair (m + 1))
      (revFullPair_sq (m + 1)) i x)
  change (relativeToPool (levPair F a) i).hom
    ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (resPair F a) i).hom _) = _
  rw [show (relativeToPool (levPair F a) i).hom
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (resPair F a) i).hom _) =
      ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (resPair F a) i) ≫
        relativeToPool (levPair F a) i).hom _ from rfl, hn]
  change (cohPullback (TopPair.Hom.fst (resPair F a)) i).hom _ = _
  rw [← incl_insert]
  exact Finsler.Cup.pullback_comp (inclE m F a) (FullLoopModel.insert (m + 1)) i _

theorem res_zero_iff (a : ℝ) (i : ℕ) (hi : (m + 1) + 1 < i) (x : H (fullComplex (m + 1)) i) :
    Hmap (resHom F a) i x = 0 ↔
      (cohPullback (inclE m F a) i).hom (HRClasses.toAbs (m + 1) i hi x) = 0 := by
  rw [← toAbsLev_res]
  have h0 : toAbsLev m F a i 0 = 0 := by
    unfold toAbsLev
    rw [LinearEquiv.map_zero, map_zero]
    rfl
  constructor
  · intro h
    rw [h, h0]
  · intro h
    exact toAbsLev_injective m F a i hi (h.trans h0.symm)

/-- A class vanishing on a longer length sublevel vanishes on the energy sublevel. -/
theorem vanish_of_length {i : ℕ} (x : cohomologyZMod2 (Loops (m + 1)) i) {a R : ℝ} (ha : 0 < a)
    (haR : a < R) (h : (cohPullback (LengthFilteredLoopRotation.full F R) i).hom x = 0) :
    (cohPullback (inclE m F a) i).hom x = 0 := by
  let ι : TopCat.of (lev F a) ⟶ TopCat.of (SelfCutOscillation.short F R) :=
    TopCat.ofHom ⟨fun u => ⟨u.1, lt_trans (StrictLengthEnergyBridge.toLength F a ha u).2 haR⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hfac : ι ≫ LengthFilteredLoopRotation.full F R = inclE m F a := rfl
  rw [← hfac, Finsler.Cup.pullback_comp]
  change (cohPullback ι i).hom ((cohPullback (LengthFilteredLoopRotation.full F R) i).hom x) = 0
  rw [h, map_zero]

/-- A class not vanishing on a length sublevel does not vanish on the energy sublevel. -/
theorem ne_of_length {i : ℕ} (x : cohomologyZMod2 (Loops (m + 1)) i) {b : ℝ} (hb : 0 < b)
    (h : (cohPullback (LengthFilteredLoopRotation.full F b) i).hom x ≠ 0) :
    (cohPullback (inclE m F b) i).hom x ≠ 0 := by
  intro h0
  apply h
  have hfac : StrictLengthEnergyBridge.toLength F b hb ≫ LengthFilteredLoopRotation.full F b =
      inclE m F b := rfl
  have h1 : (cohPullback (StrictLengthEnergyBridge.toLength F b hb) i).hom
      ((cohPullback (LengthFilteredLoopRotation.full F b) i).hom x) = 0 := by
    rw [← Finsler.Cup.pullback_comp, hfac]
    exact h0
  have hinv := Finsler.DiagonalCohomology.homotopy_pullback
    (StrictLengthEnergyBridge.shortHomotopy F b hb) i
    ((cohPullback (LengthFilteredLoopRotation.full F b) i).hom x)
  rw [Finsler.DiagonalCohomology.pullback_id, Finsler.Cup.pullback_comp, h1, map_zero] at hinv
  exact hinv

theorem exists_point : ∃ P : Sphere (m + 1), Nonempty (equator P) :=
  ⟨Finsler.SphereRetraction.northPole (m + 1),
    MeridianEquatorHomology.equator_nonempty (by omega) _⟩

/-- **HR with finitely many prime closed geodesic images**: the resonance bands `res_inj` and
`res_zero` of `BasisResidual.FillRes` for the ordinary cohomology of (Λ, M), n = m + 1 ≥ 3. -/
theorem hr_of_finite (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    ∃ α c₁ a₀ : ℝ, 0 < α ∧ 0 ≤ c₁ ∧ 0 < a₀ ∧
      (∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, c₁ < (i : ℝ) → (i : ℝ) < α * a - c₁ →
        Function.Injective (Hmap (resHom F a) i)) ∧
      (∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, α * a + c₁ < (i : ℝ) →
        ∀ x : H (fullComplex (m + 1)) i, Hmap (resHom F a) i x = 0) := by
  obtain ⟨P, ⟨v₀⟩⟩ := exists_point m
  obtain ⟨C, D, hband⟩ := FullHRAbs.band m hm F P v₀ hfin
  have hβ := NativeGHOptimalRate.rate_positive m hm F P v₀
  set β := NativeGHOptimalRate.rate m F with hβdef
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set K := 2 * (m : ℝ) / β with hK
  have hK0 : 0 < K := by positivity
  set σ := β / (2 * (m : ℝ)) with hσ
  have hσ0 : 0 < σ := by positivity
  have hKσ : K * σ = 1 := by rw [hK, hσ]; field_simp
  have hC0 := abs_nonneg C
  have hD0 := abs_nonneg D
  set c₁ := 8 * (m : ℝ) + 3 + (|C| + |D| + 1) * K with hc₁
  have hc₁σ : |C| + |D| + 1 ≤ c₁ * σ := by
    have : c₁ * σ = (8 * (m : ℝ) + 3) * σ + (|C| + |D| + 1) * (K * σ) := by rw [hc₁]; ring
    rw [this, hKσ, mul_one]
    have : 0 ≤ (8 * (m : ℝ) + 3) * σ := by positivity
    linarith
  have hc₁8 : 8 * (m : ℝ) + 3 ≤ c₁ := by
    have : 0 ≤ (|C| + |D| + 1) * K := by positivity
    linarith
  have hdeg : ∀ i : ℕ, c₁ < (i : ℝ) → (m + 1) + 1 < i ∧ 8 * m ≤ i := by
    intro i hi
    have h : ((8 * m + 3 : ℕ) : ℝ) < (i : ℝ) := by push_cast; linarith
    have h' : 8 * m + 3 < i := by exact_mod_cast h
    exact ⟨by omega, by omega⟩
  have hscale : ∀ i : ℕ, (i : ℝ) * β / (2 * m) = (i : ℝ) * σ := by
    intro i; rw [hσ]; ring
  refine ⟨K, c₁, 1, hK0, by positivity, one_pos, ?_, ?_⟩
  · intro a ha i hi1 hi2
    obtain ⟨hi, hi8⟩ := hdeg i hi1
    rw [injective_iff_map_eq_zero]
    intro x hx0
    by_contra hx
    have hx' : HRClasses.toAbs (m + 1) i hi x ≠ 0 := fun h =>
      hx ((HRClasses.toAbs (m + 1) i hi).injective (h.trans (map_zero _).symm))
    have hlt : (i : ℝ) * β / (2 * m) + D < a := by
      rw [hscale]
      have h1 : (i : ℝ) * σ < (K * a - c₁) * σ := mul_lt_mul_of_pos_right hi2 hσ0
      have h2 : (K * a - c₁) * σ = a * (K * σ) - c₁ * σ := by ring
      rw [h2, hKσ, mul_one] at h1
      have := le_abs_self D
      linarith
    have hL := (hband i hi8 _ hx').2 a hlt
    exact ne_of_length m F _ (by linarith) hL ((res_zero_iff m F a i hi x).mp hx0)
  · intro a ha i hi1 x
    have hKa : 0 < K * a := by positivity
    obtain ⟨hi, hi8⟩ := hdeg i (by linarith)
    by_cases hx : x = 0
    · rw [hx, map_zero]
    have hx' : HRClasses.toAbs (m + 1) i hi x ≠ 0 := fun h =>
      hx ((HRClasses.toAbs (m + 1) i hi).injective (h.trans (map_zero _).symm))
    have hR : a + 1 / 2 < (i : ℝ) * β / (2 * m) - C := by
      rw [hscale]
      have h1 : (K * a + c₁) * σ < (i : ℝ) * σ := mul_lt_mul_of_pos_right hi1 hσ0
      have h2 : (K * a + c₁) * σ = a * (K * σ) + c₁ * σ := by ring
      rw [h2, hKσ, mul_one] at h1
      have := le_abs_self C
      linarith
    have hz := (hband i hi8 _ hx').1 (a + 1 / 2) hR
    exact (res_zero_iff m F a i hi x).mpr (vanish_of_length m F _ (by linarith) (by linarith) hz)

end

end Finsler.HRBridge
