module

public import Finsler.Geometry.PolygonChart
public import Mathlib.Data.ZMod.Basic

/-! Iteration of closed polygons in the Hilbert coordinates. The `m`-fold iterate of a closed
polygon with `N` vertices is the polygon with `m N` vertices obtained by reduction of the index
modulo `N`. The normalized polygon energy of the iterate is `m²` times the energy. In the
Hilbert coordinates centred at a polygon and at its iterate, iteration is a linear map that
multiplies inner products by `m`, maps the centre to the centre, and is compatible with the
decoding; so the coordinate energy of the iterate at an iterated point is `m²` times the
coordinate energy. The rotation of the iterated polygon by one period is a linear isometry of
the coordinates that preserves the coordinate energy, and its fixed vectors are the iterated
vectors. No calculus is used in this file. -/

@[expose] public section

namespace Finsler.PolygonIterate

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

/-! ### Indices -/

section Index

variable (m N : ℕ)

/-- Reduction of the index of the iterated polygon modulo `N`. -/
def red : ZMod (m * N) →+* ZMod N := ZMod.castHom (Dvd.intro_left m rfl) (ZMod N)

theorem red_natCast (k : ℕ) : red m N (k : ZMod (m * N)) = (k : ZMod N) := map_natCast _ k

/-- The `m`-fold iterate of a closed polygon. -/
def iterate {α : Type*} (q : ZMod N → α) : ZMod (m * N) → α := fun i => q (red m N i)

theorem iterate_apply {α : Type*} (q : ZMod N → α) (i : ZMod (m * N)) :
    iterate m N q i = q (red m N i) := rfl

theorem iterate_natCast {α : Type*} (q : ZMod N → α) (k : ℕ) :
    iterate m N q (k : ZMod (m * N)) = q (k : ZMod N) := by
  rw [iterate_apply, red_natCast]

theorem iterate_natCast_add_one {α : Type*} (q : ZMod N → α) (k : ℕ) :
    iterate m N q ((k : ZMod (m * N)) + 1) = q ((k : ZMod N) + 1) := by
  rw [iterate_apply, map_add, map_one, red_natCast]

/-- A sum over `m` periods of a function of the index modulo `N`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (g : ZMod N → M) :
    ∑ k ∈ Finset.range (m * N), g (k : ZMod N) = m • ∑ k ∈ Finset.range N, g (k : ZMod N) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [add_one_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

/-- A sum over the residues as a sum over a range. -/
theorem sum_univ_eq_sum_range {K : ℕ} [NeZero K] {M : Type*} [AddCommMonoid M]
    (g : ZMod K → M) : ∑ i : ZMod K, g i = ∑ k ∈ Finset.range K, g (k : ZMod K) := by
  refine Finset.sum_bij' (fun a _ => a.val) (fun k _ => (k : ZMod K)) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro k _
    exact Finset.mem_univ _
  · intro a _
    exact ZMod.natCast_zmod_val a
  · intro k hk
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)
  · intro a _
    rw [ZMod.natCast_zmod_val]

end Index

/-! ### The energy of an iterate -/

section Energy

variable {n : ℕ} (m N : ℕ)

/-- The normalized polygon energy of the `m`-fold iterate is `m²` times the energy. -/
theorem polyEnergyN_iterate (F : ReversibleMetric n) (Q : ZMod N → Ambient n) :
    polyEnergyN F (m * N) (iterate m N Q) = (m : ℝ) ^ 2 * polyEnergyN F N Q := by
  have h : ∑ k ∈ Finset.range (m * N), ambientMinEnergy F
      (iterate m N Q (k : ZMod (m * N)), iterate m N Q ((k : ZMod (m * N)) + 1)) =
      m • ∑ k ∈ Finset.range N, ambientMinEnergy F (Q (k : ZMod N), Q ((k : ZMod N) + 1)) := by
    rw [← sum_range_mul m N (fun j : ZMod N => ambientMinEnergy F (Q j, Q (j + 1)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iterate_natCast, iterate_natCast_add_one]
  unfold polyEnergyN
  rw [h, nsmul_eq_mul]
  push_cast
  ring

/-- The normalized polygon energy is invariant under rotation of the index. -/
theorem polyEnergyN_add {K : ℕ} [NeZero K] (F : ReversibleMetric n) (Q : ZMod K → Ambient n)
    (s : ZMod K) : polyEnergyN F K (fun i => Q (i + s)) = polyEnergyN F K Q := by
  have h1 : ∑ k ∈ Finset.range K, ambientMinEnergy F
      (Q ((k : ZMod K) + s), Q ((k : ZMod K) + 1 + s)) =
      ∑ i : ZMod K, ambientMinEnergy F (Q (i + s), Q (i + 1 + s)) :=
    (sum_univ_eq_sum_range fun i : ZMod K => ambientMinEnergy F (Q (i + s), Q (i + 1 + s))).symm
  have h2 : ∑ k ∈ Finset.range K, ambientMinEnergy F (Q (k : ZMod K), Q ((k : ZMod K) + 1)) =
      ∑ i : ZMod K, ambientMinEnergy F (Q i, Q (i + 1)) :=
    (sum_univ_eq_sum_range fun i : ZMod K => ambientMinEnergy F (Q i, Q (i + 1))).symm
  have h3 : ∑ i : ZMod K, ambientMinEnergy F (Q (i + s), Q (i + 1 + s)) =
      ∑ i : ZMod K, ambientMinEnergy F (Q i, Q (i + 1)) := by
    rw [← Equiv.sum_comp (Equiv.addRight s) fun i : ZMod K => ambientMinEnergy F (Q i, Q (i + 1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ambientMinEnergy F (Q (i + s), Q (i + 1 + s)) =
      ambientMinEnergy F (Q (i + s), Q (i + s + 1))
    rw [add_right_comm]
  change (K : ℝ) * ∑ k ∈ Finset.range K, ambientMinEnergy F
      (Q ((k : ZMod K) + s), Q ((k : ZMod K) + 1 + s)) =
    (K : ℝ) * ∑ k ∈ Finset.range K, ambientMinEnergy F (Q (k : ZMod K), Q ((k : ZMod K) + 1))
  rw [h1, h2, h3]

end Energy

/-! ### Iteration in the Hilbert coordinates -/

section Coordinates

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

/-- Iteration in the Hilbert coordinates. -/
def iterL : Model n N →L[ℝ] Model n (m * N) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i : ZMod (m * N) => x (red m N i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem iterL_apply (x : Model n N) (i : ZMod (m * N)) : iterL m N x i = x (red m N i) := rfl

/-- Iteration multiplies inner products by `m`. -/
theorem inner_iterL (x y : Model n N) : ⟪iterL m N x, iterL m N y⟫ = (m : ℝ) * ⟪x, y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, sum_univ_eq_sum_range, sum_univ_eq_sum_range]
  have h : ∑ k ∈ Finset.range (m * N),
      ⟪iterL m N x (k : ZMod (m * N)), iterL m N y (k : ZMod (m * N))⟫ =
      m • ∑ k ∈ Finset.range N, ⟪x (k : ZMod N), y (k : ZMod N)⟫ := by
    rw [← sum_range_mul m N (fun j : ZMod N => ⟪x j, y j⟫)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iterL_apply, iterL_apply, red_natCast]
  rw [h, nsmul_eq_mul]

theorem iterL_injective : Function.Injective (iterL (n := n) m N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := inner_iterL m N x x
  rw [hx, inner_zero_left] at h
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  exact inner_self_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hm)

theorem decode_iterate (q : ZMod N → Sphere n) (x : Model n N) :
    decode (iterate m N q) (iterL m N x) = iterate m N (decode q x) := rfl

theorem base_iterate (q : ZMod N → Sphere n) : base (iterate m N q) = iterL m N (base q) := rfl

/-- The coordinate energy of the iterate at an iterated point. -/
theorem energy_iterate (F : ReversibleMetric n) (q : ZMod N → Sphere n) (x : Model n N) :
    energy F (iterate m N q) (iterL m N x) = (m : ℝ) ^ 2 * energy F q x := by
  unfold PolygonChart.energy
  rw [decode_iterate, polyEnergyN_iterate]

/-- The rotation of the iterated polygon by one period, in the Hilbert coordinates. -/
def shiftL : Model n (m * N) →L[ℝ] Model n (m * N) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun i : ZMod (m * N) => y (i + (N : ZMod (m * N))))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem shiftL_apply (y : Model n (m * N)) (i : ZMod (m * N)) :
    shiftL m N y i = y (i + (N : ZMod (m * N))) := rfl

/-- Iterated vectors are fixed by the rotation by one period. -/
theorem shiftL_iterL (x : Model n N) : shiftL m N (iterL m N x) = iterL m N x := by
  refine PiLp.ext fun i => ?_
  rw [shiftL_apply, iterL_apply, iterL_apply, map_add, red_natCast, ZMod.natCast_self, add_zero]

/-- The rotation by one period preserves inner products. -/
theorem inner_shiftL (x y : Model n (m * N)) : ⟪shiftL m N x, shiftL m N y⟫ = ⟪x, y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Equiv.sum_comp (Equiv.addRight (N : ZMod (m * N))) fun i => ⟪x i, y i⟫

/-- A vector fixed by the rotation by one period is an iterated vector. -/
theorem exists_of_shiftL_eq {y : Model n (m * N)} (hy : shiftL m N y = y) :
    ∃ x : Model n N, iterL m N x = y := by
  have hstep : ∀ i, y (i + (N : ZMod (m * N))) = y i := fun i =>
    congrArg (fun z : Model n (m * N) => z i) hy
  have hmul : ∀ (t : ℕ) (i : ZMod (m * N)),
      y (i + (t : ZMod (m * N)) * (N : ZMod (m * N))) = y i := by
    intro t
    induction t with
    | zero =>
      intro i
      rw [Nat.cast_zero, zero_mul, add_zero]
    | succ t ih =>
      intro i
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hstep, ih]
  refine ⟨WithLp.toLp 2 (fun j : ZMod N => y ((j.val : ℕ) : ZMod (m * N))), PiLp.ext fun i => ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ZMod (m * N)) = i := ⟨i.val, ZMod.natCast_zmod_val i⟩
  change y (((red m N (a : ZMod (m * N))).val : ℕ) : ZMod (m * N)) = y (a : ZMod (m * N))
  rw [red_natCast, ZMod.val_natCast]
  have h := hmul (a / N) ((a % N : ℕ) : ZMod (m * N))
  have e : ((a % N : ℕ) : ZMod (m * N)) + ((a / N : ℕ) : ZMod (m * N)) * (N : ZMod (m * N)) =
      (a : ZMod (m * N)) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div']
  rw [e] at h
  exact h.symm

/-- The coordinate energy of the iterate is invariant under the rotation by one period. -/
theorem energy_shiftL (F : ReversibleMetric n) (q : ZMod N → Sphere n) (y : Model n (m * N)) :
    energy F (iterate m N q) (shiftL m N y) = energy F (iterate m N q) y := by
  have h : decode (iterate m N q) (shiftL m N y) =
      fun i => decode (iterate m N q) y (i + (N : ZMod (m * N))) := by
    funext i
    change inverseAmbient (q (red m N i)) (y (i + (N : ZMod (m * N)))) =
      inverseAmbient (q (red m N (i + (N : ZMod (m * N))))) (y (i + (N : ZMod (m * N))))
    rw [map_add, red_natCast, ZMod.natCast_self, add_zero]
  unfold PolygonChart.energy
  rw [h, polyEnergyN_add]

end Coordinates

end

end Finsler.PolygonIterate
