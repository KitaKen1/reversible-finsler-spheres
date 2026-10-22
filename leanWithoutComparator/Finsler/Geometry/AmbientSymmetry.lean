module

public import Finsler.Geometry.AmbientPenalty
public import Finsler.Geometry.PolygonIterate

/-! Rotation and iteration of ambient polygons. The rotation of the index by s is a continuous
linear map of the space of ambient polygons; rotations compose additively, and the j-th power of
the rotation by s is the rotation by j s. The penalty and the penalized polygon energy are
invariant under rotations. Iteration is an injective continuous linear map from polygons with N
vertices to polygons with m N vertices, with the restriction to the first period as a left
inverse; the penalty of an iterated polygon is m times the penalty, so its penalized energy with
weight λ is m² times the penalized energy with weight λ / m. The iterated polygons are exactly
the polygons fixed by the rotation by one period N. Hence in the ambient space the iterated
polygons form a linear subspace, the fixed space of a linear map which preserves the penalized
energy. -/

@[expose] public section

namespace Finsler.AmbientSymmetry

open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.AmbientPenalty

noncomputable section

variable {n : ℕ}

/-! ### Rotation -/

section Rotation

variable (K : ℕ)

/-- The rotation of the index of an ambient polygon. -/
def rotA (s : ZMod K) : (ZMod K → Ambient n) →L[ℝ] (ZMod K → Ambient n) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (i + s)

theorem rotA_apply (s : ZMod K) (Q : ZMod K → Ambient n) (i : ZMod K) :
    rotA K s Q i = Q (i + s) := rfl

theorem rotA_rotA (s t : ZMod K) (Q : ZMod K → Ambient n) :
    rotA K s (rotA K t Q) = rotA K (s + t) Q := by
  funext i
  rw [rotA_apply, rotA_apply, rotA_apply, add_assoc]

theorem rotA_zero (Q : ZMod K → Ambient n) : rotA K (0 : ZMod K) Q = Q := by
  funext i
  rw [rotA_apply, add_zero]

/-- The powers of a rotation. -/
theorem rotA_pow (s : ZMod K) (j : ℕ) (Q : ZMod K → Ambient n) :
    ((rotA (n := n) K s) ^ j) Q = rotA K ((j : ZMod K) * s) Q := by
  induction j with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, rotA_zero]
    rfl
  | succ j ih =>
    rw [pow_succ']
    change rotA K s (((rotA (n := n) K s) ^ j) Q) = _
    rw [ih, rotA_rotA, Nat.cast_succ, add_mul, one_mul]
    exact congrArg (fun t : ZMod K => rotA K t Q) (add_comm _ _)

variable [NeZero K]

/-- The penalty is invariant under rotations. -/
theorem logPen_rotA (s : ZMod K) (Q : ZMod K → Ambient n) : logPen (rotA K s Q) = logPen Q :=
  Equiv.sum_comp (Equiv.addRight s) fun i => Real.log ‖Q i‖ ^ 2

/-- The penalized polygon energy is invariant under rotations. -/
theorem pen_rotA (F : ReversibleMetric n) (lam : ℝ) (s : ZMod K) (Q : ZMod K → Ambient n) :
    pen F K lam (rotA K s Q) = pen F K lam Q := by
  unfold pen
  rw [logPen_rotA]
  congr 1
  exact polyEnergyN_add F Q s

omit [NeZero K] in
/-- Rotations keep the polygons with nonzero vertices. -/
theorem rotA_ne_zero (s : ZMod K) {Q : ZMod K → Ambient n} (hQ : ∀ j, Q j ≠ 0) (j : ZMod K) :
    rotA K s Q j ≠ 0 := hQ (j + s)

end Rotation

/-! ### Iteration -/

section Iteration

variable (m N : ℕ)

/-- Iteration of ambient polygons as a continuous linear map. -/
def iterA : (ZMod N → Ambient n) →L[ℝ] (ZMod (m * N) → Ambient n) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (red m N i)

theorem iterA_apply (Q : ZMod N → Ambient n) : iterA m N Q = iterate m N Q := rfl

/-- The restriction of a polygon with m N vertices to the first period. -/
def resA : (ZMod (m * N) → Ambient n) →L[ℝ] (ZMod N → Ambient n) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj ((j.val : ℕ) : ZMod (m * N))

theorem resA_apply (Q : ZMod (m * N) → Ambient n) (j : ZMod N) :
    resA m N Q j = Q ((j.val : ℕ) : ZMod (m * N)) := rfl

/-- Iterated polygons are fixed by the rotation by one period. -/
theorem rotA_iterate (q : ZMod N → Ambient n) :
    rotA (m * N) (N : ZMod (m * N)) (iterate m N q) = iterate m N q := by
  funext i
  rw [rotA_apply, iterate_apply, iterate_apply, map_add, red_natCast, ZMod.natCast_self,
    add_zero]

/-- Iteration keeps the polygons with nonzero vertices. -/
theorem iterate_ne_zero {Q : ZMod N → Ambient n} (hQ : ∀ j, Q j ≠ 0) (i : ZMod (m * N)) :
    iterate m N Q i ≠ 0 := hQ (red m N i)

variable [NeZero m] [NeZero N]

omit [NeZero m] in
theorem resA_iterA (Q : ZMod N → Ambient n) : resA m N (iterA m N Q) = Q := by
  funext j
  rw [resA_apply, iterA_apply, iterate_natCast, ZMod.natCast_zmod_val]

omit [NeZero m] in
theorem iterA_injective : Function.Injective (iterA (n := n) m N) := fun Q Q' h => by
  rw [← resA_iterA m N Q, ← resA_iterA m N Q', h]

/-- The penalty of an iterated polygon. -/
theorem logPen_iterate (Q : ZMod N → Ambient n) :
    logPen (iterate m N Q) = (m : ℝ) * logPen Q := by
  unfold logPen
  rw [sum_univ_eq_sum_range, sum_univ_eq_sum_range]
  have h := sum_range_mul m N (fun j : ZMod N => Real.log ‖Q j‖ ^ 2)
  rw [nsmul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_natCast]

/-- The penalized energy of an iterated polygon: m² times the penalized energy with the weight
divided by m. -/
theorem pen_iterate (F : ReversibleMetric n) (lam : ℝ) (Q : ZMod N → Ambient n) :
    pen F (m * N) lam (iterate m N Q) = (m : ℝ) ^ 2 * pen F N (lam / m) Q := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  unfold pen
  rw [polyEnergyN_iterate, logPen_iterate]
  field_simp

/-- A polygon fixed by the rotation by one period is an iterated polygon. -/
theorem exists_of_rotA_eq {Q : ZMod (m * N) → Ambient n}
    (hQ : rotA (m * N) (N : ZMod (m * N)) Q = Q) : iterA m N (resA m N Q) = Q := by
  have hstep : ∀ i, Q (i + (N : ZMod (m * N))) = Q i := fun i => congrFun hQ i
  have hmul : ∀ (t : ℕ) (i : ZMod (m * N)),
      Q (i + (t : ZMod (m * N)) * (N : ZMod (m * N))) = Q i := by
    intro t
    induction t with
    | zero =>
      intro i
      rw [Nat.cast_zero, zero_mul, add_zero]
    | succ t ih =>
      intro i
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hstep, ih]
  funext i
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ZMod (m * N)) = i := ⟨i.val, ZMod.natCast_zmod_val i⟩
  change Q (((red m N (a : ZMod (m * N))).val : ℕ) : ZMod (m * N)) = Q (a : ZMod (m * N))
  rw [red_natCast, ZMod.val_natCast]
  have h := hmul (a / N) ((a % N : ℕ) : ZMod (m * N))
  have e : ((a % N : ℕ) : ZMod (m * N)) + ((a / N : ℕ) : ZMod (m * N)) * (N : ZMod (m * N)) =
      (a : ZMod (m * N)) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div']
  rw [e] at h
  exact h.symm

/-- The fixed polygons of the rotation by one period are the iterated polygons. -/
theorem rotA_eq_iff (Q : ZMod (m * N) → Ambient n) :
    rotA (m * N) (N : ZMod (m * N)) Q = Q ↔ ∃ q : ZMod N → Ambient n, iterate m N q = Q :=
  ⟨fun h => ⟨resA m N Q, exists_of_rotA_eq m N h⟩, fun ⟨q, hq⟩ => hq ▸ rotA_iterate m N q⟩

end Iteration

end

end Finsler.AmbientSymmetry
