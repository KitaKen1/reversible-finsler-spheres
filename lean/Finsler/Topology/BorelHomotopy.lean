module

public import Finsler.Topology.BorelGraded

/-! Homogeneous equivariant linear families induce operators on the explicit reflection total complex. A proved componentwise Leibniz identity gives a total cochain homotopy, preserving support and making the induced positive-degree map zero on cohomology. -/

@[expose] public section

namespace Finsler.BorelHomotopy
open Finsler.BorelCochain Finsler.BorelGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A homogeneous equivariant linear family; differential compatibility is not required. -/
structure Family (K L : InvComplex) (m : ℕ) where
  f : ∀ j, K.C j →ₗ[ZMod 2] L.C (m+j)
  comm_t : ∀ j x, L.t (m+j) (f j x) = f j (K.t j x)

variable {K L : InvComplex} {m : ℕ} (H : Family K L m)

def total : Seq K →ₗ[ZMod 2] Seq L where
  toFun c j := if h : m ≤ j then castC L (by omega) (H.f (j-m) (c (j-m))) else 0
  map_add' c b := by
    funext j
    by_cases h : m ≤ j <;> simp [h, map_add]
  map_smul' r c := by
    funext j
    by_cases h : m ≤ j <;> simp [h, map_smul]

theorem cast_f {a b : ℕ} (h : a=b) (x : K.C a) :
    castC L (congrArg (m+·) h) (H.f a x) = H.f b (castC K h x) := by
  subst b
  rfl

theorem total_at (c : Seq K) (j : ℕ) : total H c (m+j) = H.f j (c j) := by
  change (if h : m ≤ m+j then castC L (by omega) (H.f (m+j-m) (c (m+j-m))) else 0) = _
  rw [dite_eq_left (show m ≤ m+j by omega)]
  have h : m+j-m=j := by omega
  exact (cast_f H h (c (m+j-m))).trans (congrArg (H.f j) (BorelGraded.cast_seq h c).symm)

theorem total_below (c : Seq K) {j : ℕ} (h : j < m) : total H c j = 0 := by
  change (if h : m ≤ j then _ else 0) = 0
  rw [dite_eq_right (show ¬ m ≤ j by omega)]

theorem total_low {q : ℕ} {c : Seq K} (hc : c ∈ low K q) : total H c ∈ low L (m+q) := by
  intro j hj
  have hp : m ≤ j := by omega
  have hq : q ≤ j-m := by omega
  change (if h : m ≤ j then _ else 0) = 0
  rw [dite_eq_left hp, hc (j-m) hq, map_zero, map_zero]

theorem comm_tr (j : ℕ) (x : K.C j) :
    tr L (m+j) (H.f j x) = H.f j (tr K j x) := by
  rw [tr_apply, tr_apply, map_add, H.comm_t]

/-- The ordinary Leibniz identity gives the homotopy on the entire reflection total complex. -/
theorem total_D (A : BorelGraded.Map K L (m+1))
    (hd : ∀ j x, L.d (m+j) (H.f j x) =
      castC L (by omega) (A.f j x) +
      castC L (Nat.add_assoc m j 1).symm (H.f (j+1) (K.d j x)))
    (c : Seq K) : D L (total H c) = BorelGraded.total A c + total H (D K c) := by
  funext j
  change D L (total H c) j = BorelGraded.total A c j + total H (D K c) j
  by_cases h : m ≤ j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      rw [BorelGraded.total_below A c (by omega), zero_add]
      cases m with
      | zero =>
        change tr L (0+0) (total H c (0+0)) = total H (D K c) (0+0)
        rw [total_at, total_at, D_zero, comm_tr]
      | succ m =>
        rw [D_succ, total_below H c (by omega), map_zero, zero_add]
        change tr L ((m+1)+0) (total H c ((m+1)+0)) = total H (D K c) ((m+1)+0)
        rw [total_at, total_at, D_zero, comm_tr]
    | succ k =>
      rw [show m+(k+1)=m+k+1 by omega, D_succ, total_at, hd]
      have ht : ∀ z : Seq K, total H z (m+k+1) =
          castC L (Nat.add_assoc m k 1).symm (H.f (k+1) (z (k+1))) := by
        intro z
        exact (BorelGraded.cast_seq (Nat.add_assoc m k 1).symm (total H z)).trans
          (congrArg (castC L (Nat.add_assoc m k 1).symm) (total_at H z (k+1)))
      have ha : BorelGraded.total A c (m+k+1) =
          castC L (by omega) (A.f k (c k)) := by
        exact (BorelGraded.cast_seq (show (m+1)+k=m+k+1 by omega) (BorelGraded.total A c)).trans
          (congrArg (castC L (show (m+1)+k=m+k+1 by omega)) (BorelGraded.total_at A c k))
      rw [ht, ht, ha, D_succ, map_add, map_add, BorelGraded.cast_tr, comm_tr]
      exact add_assoc _ _ _
  · have hlt : j < m := by omega
    rw [total_below H (D K c) hlt, BorelGraded.total_below A c (by omega), zero_add]
    cases j with
    | zero => rw [D_zero, total_below H c hlt, map_zero]
    | succ j => rw [D_succ, total_below H c (by omega), total_below H c hlt, map_zero, map_zero, add_zero]

theorem onHR_zero (A : BorelGraded.Map K L (m+1))
    (hd : ∀ j x, L.d (m+j) (H.f j x) =
      castC L (by omega) (A.f j x) +
      castC L (Nat.add_assoc m j 1).symm (H.f (j+1) (K.d j x)))
    (q : ℕ) (x : HR K q) : BorelGraded.onHR A q x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [BorelGraded.onHR_mk, Submodule.Quotient.mk_eq_zero]
  refine ⟨total H (c : Seq K), ?_, ?_⟩
  · change total H c.val ∈ low L ((m+1)+q)
    have h := total_low H ((mem_bcocycles K).mp c.2).1
    simpa only [show m+(q+1)=(m+1)+q by omega] using h
  · change D L (total H (c : Seq K)) = BorelGraded.total A (c : Seq K)
    rw [total_D H A hd, ((mem_bcocycles K).mp c.2).2, map_zero, add_zero]
end
end Finsler.BorelHomotopy
