module

public import Finsler.Geometry.RoundPolygon
public import Finsler.Geometry.RoundFourier

/-! Global linear coordinates around the critical manifolds of the round polygon energy.

The Fourier coefficients A_j(Q) = (2/N) Σ_k cos(2πjk/N) Q_k and B_j(Q) = (2/N) Σ_k sin(2πjk/N) Q_k
(0 < 2j < N) of an ambient polygon recover the coefficients of the modes: for 0 ≤ 2j' < N,
A_j(regular N j' a b) = [j = j'] a and B_j(regular N j' a b) = [j = j'] b, by the discrete
orthogonality relations. Hence every polygon splits uniquely as Q = regular N m (A_m Q) (B_m Q) + V
with V in the kernel of (A_m, B_m), and (Q ↦ ((A_m Q, B_m Q), V)) is a linear isomorphism of the
polygon space with Ambient² × ker(A_m, B_m). The regular m-gons are the points with orthonormal
(A_m, B_m) and V = 0, so these are global linear coordinates near the critical manifold: no
tubular neighbourhood theorem and no inverse function theorem is needed. -/

@[expose] public section

namespace Finsler.RoundCoords

open Finsler.SphereGeometry Finsler.RoundPolygon Finsler.RoundFourier Finsler.PolygonIterate
open Finset
open scoped RealInnerProductSpace Real

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-- The cosine coefficient of frequency j. -/
def coefA (j : ℕ) (Q : ZMod N → Ambient n) : Ambient n :=
  (2 / N : ℝ) • ∑ k ∈ range N, Real.cos (2 * π * j / N * k) • Q (k : ZMod N)

/-- The sine coefficient of frequency j. -/
def coefB (j : ℕ) (Q : ZMod N → Ambient n) : Ambient n :=
  (2 / N : ℝ) • ∑ k ∈ range N, Real.sin (2 * π * j / N * k) • Q (k : ZMod N)

theorem coefA_add (j : ℕ) (Q Q' : ZMod N → Ambient n) :
    coefA j (Q + Q') = coefA j Q + coefA j Q' := by
  simp only [coefA, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem coefA_smul (j : ℕ) (r : ℝ) (Q : ZMod N → Ambient n) :
    coefA j (r • Q) = r • coefA j Q := by
  simp only [coefA, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ring

theorem coefB_add (j : ℕ) (Q Q' : ZMod N → Ambient n) :
    coefB j (Q + Q') = coefB j Q + coefB j Q' := by
  simp only [coefB, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem coefB_smul (j : ℕ) (r : ℝ) (Q : ZMod N → Ambient n) :
    coefB j (r • Q) = r • coefB j Q := by
  simp only [coefB, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ring

/-- The cosine coefficient as a linear map. -/
def coefAL (j : ℕ) : (ZMod N → Ambient n) →ₗ[ℝ] Ambient n where
  toFun := coefA j
  map_add' := coefA_add j
  map_smul' := coefA_smul j

/-- The sine coefficient as a linear map. -/
def coefBL (j : ℕ) : (ZMod N → Ambient n) →ₗ[ℝ] Ambient n where
  toFun := coefB j
  map_add' := coefB_add j
  map_smul' := coefB_smul j

/-- The vertices of a mode at natural indices. -/
theorem regular_apply_natCast (j : ℕ) (a b : Ambient n) (k : ℕ) :
    regular N j a b (k : ZMod N) =
      Real.cos (2 * π * j / N * k) • a + Real.sin (2 * π * j / N * k) • b := by
  rw [regular_natCast]
  rfl

/-- The cosine coefficients of a mode. -/
theorem coefA_regular {j j' : ℕ} (hj0 : 0 < j) (hj : 2 * j < N) (hj' : 2 * j' < N)
    (a b : Ambient n) : coefA j (regular N j' a b) = if j = j' then a else 0 := by
  have hN : 0 < N := Nat.pos_of_neZero N
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold coefA
  simp only [regular_apply_natCast, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]
  rw [sum_cos_cos hN hj hj', sum_cos_sin hN hj hj', mul_zero, zero_smul, add_zero]
  by_cases h : j = j'
  · subst h
    rw [if_pos rfl, if_neg (by omega), if_pos rfl]
    rw [show (2 / N : ℝ) * (N / 2) = 1 by field_simp, one_smul]
  · rw [if_neg h, if_neg h, mul_zero, zero_smul]

/-- The sine coefficients of a mode. -/
theorem coefB_regular {j j' : ℕ} (hj0 : 0 < j) (hj : 2 * j < N) (hj' : 2 * j' < N)
    (a b : Ambient n) : coefB j (regular N j' a b) = if j = j' then b else 0 := by
  have hN : 0 < N := Nat.pos_of_neZero N
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold coefB
  simp only [regular_apply_natCast, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul]
  have hcs : ∑ k ∈ range N, Real.sin (2 * π * j / N * k) * Real.cos (2 * π * j' / N * k) = 0 := by
    have h := sum_cos_sin hN hj' hj
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hcs, mul_zero, zero_smul, zero_add]
  by_cases hj'0 : j' = 0
  · subst hj'0
    have hz : ∑ k ∈ range N, Real.sin (2 * π * j / N * k) *
        Real.sin (2 * π * ((0 : ℕ) : ℝ) / N * k) = 0 := by simp
    rw [hz, mul_zero, zero_smul, if_neg (by omega)]
  · rw [sum_sin_sin hN hj0 hj hj']
    by_cases h : j = j'
    · subst h
      rw [if_pos rfl, if_pos rfl]
      rw [show (2 / N : ℝ) * (N / 2) = 1 by field_simp, one_smul]
    · rw [if_neg h, if_neg h, mul_zero, zero_smul]

/-! ### The splitting at the frequency m -/

/-- The polygons without the frequency m. -/
def kern (m : ℕ) : Submodule ℝ (ZMod N → Ambient n) :=
  LinearMap.ker (coefAL (n := n) (N := N) m) ⊓ LinearMap.ker (coefBL m)

theorem mem_kern {m : ℕ} {V : ZMod N → Ambient n} :
    V ∈ kern m ↔ coefA m V = 0 ∧ coefB m V = 0 := by
  simp [kern, coefAL, coefBL]

/-- The regular part of a polygon at the frequency m. -/
def regPart (m : ℕ) (Q : ZMod N → Ambient n) : ZMod N → Ambient n :=
  regular N m (coefA m Q) (coefB m Q)

theorem regular_add (j : ℕ) (a b a' b' : Ambient n) :
    regular N j (a + a') (b + b') = regular N j a b + regular N j a' b' := by
  funext i
  simp only [regular, circ, Pi.add_apply, smul_add]
  abel

theorem regular_smul (j : ℕ) (r : ℝ) (a b : Ambient n) :
    regular N j (r • a) (r • b) = r • regular N j a b := by
  funext i
  simp only [regular, circ, Pi.smul_apply, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem rest_mem_kern {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N) (Q : ZMod N → Ambient n) :
    Q - regPart m Q ∈ kern m := by
  rw [mem_kern]
  have hA := coefA_regular (N := N) hm hmN hmN (coefA m Q) (coefB m Q)
  have hB := coefB_regular (N := N) hm hmN hmN (coefA m Q) (coefB m Q)
  rw [if_pos rfl] at hA hB
  constructor
  · rw [sub_eq_add_neg, coefA_add, ← neg_one_smul ℝ (regPart m Q), coefA_smul, regPart, hA]
    simp
  · rw [sub_eq_add_neg, coefB_add, ← neg_one_smul ℝ (regPart m Q), coefB_smul, regPart, hB]
    simp

/-- The global linear coordinates at the frequency m. -/
def coords (m : ℕ) (hm : 0 < m) (hmN : 2 * m < N) :
    (ZMod N → Ambient n) ≃ₗ[ℝ] (Ambient n × Ambient n) × kern (n := n) (N := N) m where
  toFun Q := ((coefA m Q, coefB m Q), ⟨Q - regPart m Q, rest_mem_kern hm hmN Q⟩)
  invFun p := regular N m p.1.1 p.1.2 + (p.2 : ZMod N → Ambient n)
  map_add' Q Q' := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp only [coefA_add, coefB_add, Prod.fst_add, Prod.mk_add_mk]
    · simp only [Prod.snd_add, Submodule.coe_add, regPart, coefA_add, coefB_add, regular_add]
      abel
  map_smul' r Q := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp only [coefA_smul, coefB_smul, RingHom.id_apply, Prod.smul_fst, Prod.smul_mk]
    · simp only [RingHom.id_apply, Prod.smul_snd, Submodule.coe_smul, regPart, coefA_smul,
        coefB_smul, regular_smul, smul_sub]
  left_inv Q := by
    change regular N m (coefA m Q) (coefB m Q) + (Q - regPart m Q) = Q
    simp only [regPart]
    abel
  right_inv p := by
    obtain ⟨⟨a, b⟩, V, hV⟩ := p
    rw [mem_kern] at hV
    have hA := coefA_regular (N := N) hm hmN hmN a b
    have hB := coefB_regular (N := N) hm hmN hmN a b
    rw [if_pos rfl] at hA hB
    have h1 : coefA m (regular N m a b + V) = a := by rw [coefA_add, hA, hV.1, add_zero]
    have h2 : coefB m (regular N m a b + V) = b := by rw [coefB_add, hB, hV.2, add_zero]
    ext1
    · simp only [h1, h2]
    · apply Subtype.ext
      simp only [regPart, h1, h2]
      abel

theorem coords_regular {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N) (x u : Ambient n) :
    coords m hm hmN (regular N m x u) = ((x, u), 0) := by
  have hA := coefA_regular (N := N) hm hmN hmN x u
  have hB := coefB_regular (N := N) hm hmN hmN x u
  rw [if_pos rfl] at hA hB
  ext1
  · change (coefA m (regular N m x u), coefB m (regular N m x u)) = (x, u)
    rw [hA, hB]
  · apply Subtype.ext
    change regular N m x u - regPart m (regular N m x u) = 0
    simp only [regPart, hA, hB, sub_self]

end

end Finsler.RoundCoords
