module

public import Finsler.Geometry.GeodesicUnique
public import Finsler.Geometry.PrimeRepresentative
public import Finsler.Analysis.IntervalH1GeodesicCritical

/-! Critical levels. The prime levels are the numbers √E of the prime closed geodesics; two prime
closed geodesics with the same image have the same energy, so with finitely many prime closed
geodesic images there are finitely many prime levels, all positive. The set of critical levels is
the set of numbers 2^m √E(u) for tangent critical loops u of positive energy and m ≥ 0; it is
closed under doubling by definition, positive, and contains √E of every tangent critical loop of
positive energy. Every tangent critical loop of positive energy is an iterate of a prime closed
geodesic, so every critical level is an integer multiple of a prime level, and with finitely many
prime closed geodesic images every bounded interval contains finitely many critical levels.
Choosing one prime closed geodesic for each prime image, every tangent critical loop of positive
energy is a rotation, or the reversal of a rotation, of an iterate of a chosen one. -/

@[expose] public section

namespace Finsler.CriticalLevels

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SmoothSobolev
open Finsler.SobolevCurveVariation
open Set

noncomputable section

variable {n : ℕ}

/-- A prime closed geodesic with a given prime image. -/
def chosen (F : ReversibleMetric n) (s : Set (Sphere n)) (hs : s ∈ primeImages F) :
    ClosedGeodesic F :=
  Exists.choose hs

theorem chosen_prime (F : ReversibleMetric n) (s : Set (Sphere n)) (hs : s ∈ primeImages F) :
    Finsler.Geodesics.Prime (chosen F s hs) :=
  (Exists.choose_spec hs).1

theorem chosen_image (F : ReversibleMetric n) (s : Set (Sphere n)) (hs : s ∈ primeImages F) :
    Finsler.Loops.image (chosen F s hs).loop = s :=
  (Exists.choose_spec hs).2

/-- The levels √E of the prime closed geodesics. -/
def primeLevels (F : ReversibleMetric n) : Set ℝ :=
  {l | ∃ γ : ClosedGeodesic F, Finsler.Geodesics.Prime γ ∧
    Real.sqrt (Finsler.LoopEnergy.energy F γ.loop) = l}

theorem primeLevels_pos (F : ReversibleMetric n) {l : ℝ} (hl : l ∈ primeLevels F) : 0 < l := by
  obtain ⟨γ, -, rfl⟩ := hl
  exact Real.sqrt_pos.mpr (regular_energy_pos F γ.loop γ.regular)

/-- With finitely many prime closed geodesic images there are finitely many prime levels. -/
theorem primeLevels_finite (F : ReversibleMetric n) (hfin : (primeImages F).Finite) :
    (primeLevels F).Finite := by
  have h := hfin.dependent_image
    (fun s hs => Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop))
  refine h.subset ?_
  rintro l ⟨γ, hγ, rfl⟩
  have hmem : Finsler.Loops.image γ.loop ∈ primeImages F := prime_image_mem γ hγ
  refine ⟨_, hmem, ?_⟩
  rw [Finsler.GeodesicUnique.energy_eq_of_image_eq γ (chosen F _ hmem) hγ
    (chosen_prime F _ hmem) (chosen_image F _ hmem).symm]

theorem iterate_shift (γ : SmoothLoop n) (a : ℝ) {k : ℕ} (hk : k ≠ 0) :
    iterate (shift γ a) k = shift (iterate γ k) (a / k) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  apply loop_ext
  intro t
  change γ ((k : ℝ) * t + a) = γ ((k : ℝ) * (t + a / k))
  rw [mul_add, mul_div_cancel₀ a hk']

theorem iterate_reverse (γ : SmoothLoop n) (k : ℕ) :
    iterate (reverse γ) k = reverse (iterate γ k) := by
  apply loop_ext
  intro t
  change γ (-((k : ℝ) * t)) = γ ((k : ℝ) * -t)
  rw [mul_neg]

/-- Every closed geodesic is a rotation, or the reversal of a rotation, of an iterate of the
chosen prime closed geodesic with the same image. -/
theorem closedGeodesic_eq_chosen_iterate (F : ReversibleMetric n) (g : ClosedGeodesic F) :
    ∃ (s : Set (Sphere n)) (hs : s ∈ primeImages F) (k : ℕ) (a : ℝ), 0 < k ∧
      (g.loop = shift (iterate (chosen F s hs).loop k) a ∨
        g.loop = reverse (shift (iterate (chosen F s hs).loop k) a)) := by
  obtain ⟨δ, k, hk, hprime, hit, -⟩ := exists_prime_representative g
  obtain ⟨s, hs, hsimg⟩ : ∃ s, ∃ _ : s ∈ primeImages F, Finsler.Loops.image δ.loop = s :=
    ⟨_, prime_image_mem δ hprime, rfl⟩
  obtain ⟨a, h | h⟩ := Finsler.GeodesicUnique.shift_or_reverse_of_image_eq (chosen F s hs) δ
    (chosen_prime F s hs) hprime ((chosen_image F s hs).trans hsimg.symm)
  · refine ⟨s, hs, k, a / k, hk, Or.inl ?_⟩
    rw [← hit, h, iterate_shift _ _ (Nat.ne_of_gt hk)]
  · refine ⟨s, hs, k, a / k, hk, Or.inr ?_⟩
    rw [← hit, h, iterate_reverse, iterate_shift _ _ (Nat.ne_of_gt hk)]

/-- With the chosen prime closed geodesics, one for each prime image: every tangent critical
loop of positive energy is a rotation, or the reversal of a rotation, of an iterate of one of
them. -/
theorem critical_eq_chosen_iterate (F : ReversibleMetric n) (u : SphereLoop n)
    (hu : TangentCritical F u) (hE : 0 < energy F u) :
    ∃ (s : Set (Sphere n)) (hs : s ∈ primeImages F) (k : ℕ) (a : ℝ), 0 < k ∧
      (u = ofSmooth (shift (iterate (chosen F s hs).loop k) a) ∨
        u = ofSmooth (reverse (shift (iterate (chosen F s hs).loop k) a))) := by
  obtain ⟨g, rfl⟩ :=
    (Finsler.SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic F u hE).mp hu
  obtain ⟨s, hs, k, a, hk, h | h⟩ := closedGeodesic_eq_chosen_iterate F g
  · exact ⟨s, hs, k, a, hk, Or.inl (congrArg ofSmooth h)⟩
  · exact ⟨s, hs, k, a, hk, Or.inr (congrArg ofSmooth h)⟩

/-- The critical levels: the numbers 2^m √E(u) for tangent critical loops u of positive
energy. -/
def crit (F : ReversibleMetric n) : Set ℝ :=
  {c | ∃ u : SphereLoop n, TangentCritical F u ∧ 0 < energy F u ∧
    ∃ m : ℕ, c = 2 ^ m * Real.sqrt (energy F u)}

theorem crit_pos (F : ReversibleMetric n) {c : ℝ} (hc : c ∈ crit F) : 0 < c := by
  obtain ⟨u, -, hE, m, rfl⟩ := hc
  exact mul_pos (pow_pos two_pos m) (Real.sqrt_pos.mpr hE)

theorem crit_mem (F : ReversibleMetric n) (u : SphereLoop n) (hu : TangentCritical F u)
    (hE : 0 < energy F u) : Real.sqrt (energy F u) ∈ crit F :=
  ⟨u, hu, hE, 0, by rw [pow_zero, one_mul]⟩

theorem crit_double (F : ReversibleMetric n) {c : ℝ} (hc : c ∈ crit F) : 2 * c ∈ crit F := by
  obtain ⟨u, hu, hE, m, rfl⟩ := hc
  exact ⟨u, hu, hE, m + 1, by rw [pow_succ]; ring⟩

/-- Every critical level is an integer multiple of a prime level. -/
theorem crit_eq_multiple (F : ReversibleMetric n) {c : ℝ} (hc : c ∈ crit F) :
    ∃ l ∈ primeLevels F, ∃ j : ℕ, c = j * l := by
  obtain ⟨u, hu, hE, m, rfl⟩ := hc
  obtain ⟨g, rfl⟩ :=
    (Finsler.SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic F u hE).mp hu
  obtain ⟨δ, k, -, hprime, hit, -⟩ := exists_prime_representative g
  refine ⟨_, ⟨δ, hprime, rfl⟩, 2 ^ m * k, ?_⟩
  rw [energy_ofSmooth, ← hit, Finsler.LoopEnergy.energy_iterate,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)]
  push_cast
  ring

/-- With finitely many prime closed geodesic images every bounded interval contains finitely
many critical levels. -/
theorem crit_finite (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (a b : ℝ) :
    (crit F ∩ Icc a b).Finite := by
  have hP := primeLevels_finite F hfin
  have hU : (⋃ l ∈ primeLevels F,
      (fun j : ℕ => (j : ℝ) * l) '' {j : ℕ | j ≤ ⌊b / l⌋₊}).Finite :=
    hP.biUnion fun l _ => (Set.finite_le_nat _).image _
  refine hU.subset ?_
  rintro c ⟨hc, -, hcb⟩
  obtain ⟨l, hl, j, rfl⟩ := crit_eq_multiple F hc
  have hlpos := primeLevels_pos F hl
  exact mem_iUnion₂.mpr ⟨l, hl, j, Nat.le_floor ((le_div_iff₀ hlpos).mpr hcb), rfl⟩

end

end Finsler.CriticalLevels
