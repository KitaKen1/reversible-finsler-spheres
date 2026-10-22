module

public import Finsler.Topology.BorelCochain

/-! Degree-shifting equivariant cochain maps on the explicit reflection Borel complex.
The component formula, differential compatibility, quotient action, w and
naturality are proved for all degrees, including zero. -/

@[expose] public section

namespace Finsler.BorelGraded
open Finsler.BorelCochain
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def castC (K : InvComplex) {a b : ℕ} (h : a = b) : K.C a →ₗ[ZMod 2] K.C b := by
  subst b
  exact LinearMap.id

@[simp] theorem castC_rfl (K : InvComplex) (a : ℕ) (x : K.C a) : castC K rfl x = x := rfl

structure Map (K L : InvComplex) (p : ℕ) where
  f : ∀ j, K.C j →ₗ[ZMod 2] L.C (p + j)
  comm_d : ∀ j x, L.d (p + j) (f j x) =
    castC L (Nat.add_assoc p j 1).symm (f (j + 1) (K.d j x))
  comm_t : ∀ j x, L.t (p + j) (f j x) = f j (K.t j x)

variable {K L : InvComplex} {p : ℕ} (A : Map K L p)

def total : Seq K →ₗ[ZMod 2] Seq L where
  toFun c j := if h : p ≤ j then castC L (by omega) (A.f (j-p) (c (j-p))) else 0
  map_add' c b := by
    funext j
    by_cases h : p ≤ j <;> simp [h, map_add]
  map_smul' r c := by
    funext j
    by_cases h : p ≤ j <;> simp [h, map_smul]

theorem cast_f {a b : ℕ} (h : a=b) (x : K.C a) :
    castC L (congrArg (p+·) h) (A.f a x) = A.f b (castC K h x) := by
  subst b
  rfl

theorem cast_seq {a b : ℕ} (h : a=b) (c : Seq L) : c b = castC L h (c a) := by
  subst b
  rfl

theorem total_apply (c : Seq K) (j : ℕ) : total A c j =
    if h : p ≤ j then castC L (by omega) (A.f (j-p) (c (j-p))) else 0 := rfl

theorem total_at (c : Seq K) (j : ℕ) : total A c (p+j) = A.f j (c j) := by
  rw [total_apply, dite_eq_left (show p ≤ p+j by omega)]
  have h : p+j-p=j := by omega
  exact (cast_f A h (c (p+j-p))).trans (congrArg (A.f j) (cast_seq h c).symm)

theorem total_below (c : Seq K) {j : ℕ} (h : j < p) : total A c j = 0 := by
  rw [total_apply, dite_eq_right (show ¬ p ≤ j by omega)]

theorem total_low {q : ℕ} {c : Seq K} (hc : c ∈ low K q) : total A c ∈ low L (p+q) := by
  intro j hj
  have hp : p ≤ j := by omega
  have hq : q ≤ j-p := by omega
  rw [total_apply, dite_eq_left hp, hc (j-p) hq, map_zero, map_zero]

theorem comm_tr (j : ℕ) (x : K.C j) :
    tr L (p+j) (A.f j x) = A.f j (tr K j x) := by
  rw [tr_apply, tr_apply, map_add, A.comm_t]

theorem cast_d {a b : ℕ} (h : a=b) (x : L.C a) :
    L.d b (castC L h x) = castC L (congrArg (·+1) h) (L.d a x) := by
  subst b
  rfl

theorem cast_tr {a b : ℕ} (h : a=b) (x : L.C a) :
    tr L b (castC L h x) = castC L h (tr L a x) := by
  subst b
  rfl

theorem total_D (c : Seq K) : D L (total A c) = total A (D K c) := by
  funext j
  by_cases h : p ≤ j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      cases p with
      | zero =>
        change tr L (0+0) (total A c (0+0)) = total A (D K c) (0+0)
        rw [total_at, total_at, D_zero, comm_tr]
      | succ p =>
        rw [D_succ, total_below A c (by omega), map_zero, zero_add]
        change tr L ((p+1)+0) (total A c ((p+1)+0)) = total A (D K c) ((p+1)+0)
        rw [total_at, total_at, D_zero, comm_tr]
    | succ k =>
      rw [show p + (k+1) = p+k+1 by omega, D_succ, total_at]
      have ht : ∀ z : Seq K, total A z (p+k+1) =
          castC L (Nat.add_assoc p k 1).symm (A.f (k+1) (z (k+1))) := by
        intro z
        exact (cast_seq (Nat.add_assoc p k 1).symm (total A z)).trans
          (congrArg (castC L (Nat.add_assoc p k 1).symm) (total_at A z (k+1)))
      rw [A.comm_d, ht, ht, D_succ, map_add, map_add]
      have htr : ∀ x : L.C (p+(k+1)),
          tr L (p+k+1) (castC L (Nat.add_assoc p k 1).symm x) =
            castC L (Nat.add_assoc p k 1).symm (tr L (p+(k+1)) x) := by
        intro x
        exact cast_tr (Nat.add_assoc p k 1).symm x
      rw [htr, comm_tr]
  · have hlt : j < p := by omega
    rw [total_below A (D K c) hlt]
    cases j with
    | zero => rw [D_zero, total_below A c hlt, map_zero]
    | succ j => rw [D_succ, total_below A c (by omega), total_below A c hlt, map_zero, map_zero, add_zero]

theorem total_single (q : ℕ) (x : K.C q) :
    total A (Pi.single q x) = Pi.single (p+q) (A.f q x) := by
  funext j
  by_cases hj : p ≤ j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [total_at]
    by_cases hk : k=q
    · subst k
      rw [single_same, single_same]
    · rw [single_ne K hk, map_zero, single_ne L (show p+k≠p+q by omega)]
  · rw [total_below A _ (by omega), single_ne L (show j≠p+q by omega)]

/-- A homogeneous equivariant cochain map acts on Borel cocycles. -/
def cyclesMap (q : ℕ) : bcocycles K q →ₗ[ZMod 2] bcocycles L (p+q) :=
  LinearMap.codRestrict (bcocycles L (p+q)) (total A ∘ₗ (bcocycles K q).subtype) (fun c => by
    refine ⟨?_, ?_⟩
    · change total A (c : Seq K) ∈ low L (p+q+1)
      have h := total_low A ((mem_bcocycles K).mp c.2).1
      simpa only [← Nat.add_assoc] using h
    · change D L (total A (c : Seq K)) = 0
      rw [total_D, ((mem_bcocycles K).mp c.2).2, map_zero])

theorem cyclesMap_boundary (q : ℕ) :
    (bcoboundaries K q).comap (bcocycles K q).subtype ≤
      ((bcoboundaries L (p+q)).comap (bcocycles L (p+q)).subtype).comap (cyclesMap A q) := by
  rintro c ⟨b, hb, hbc⟩
  refine ⟨total A b, total_low A hb, ?_⟩
  change D L (total A b) = total A (c : Seq K)
  rw [total_D]
  exact congrArg (total A) hbc

/-- Degree-p action on the actual quotient, with boundary preservation proved. -/
def onHR (q : ℕ) : HR K q →ₗ[ZMod 2] HR L (p+q) :=
  Submodule.mapQ _ _ (cyclesMap A q) (cyclesMap_boundary A q)

theorem onHR_mk (q : ℕ) (c : bcocycles K q) :
    onHR A q (Submodule.Quotient.mk c) = Submodule.Quotient.mk (cyclesMap A q c) := rfl

def castHR {a b : ℕ} (h : a=b) : HR L a →ₗ[ZMod 2] HR L b := by
  subst b
  exact LinearMap.id

theorem castHR_mk {a b : ℕ} (h : a=b) (c : Seq L)
    (ha : c ∈ bcocycles L a) (hb : c ∈ bcocycles L b) :
    castHR h (Submodule.Quotient.mk (⟨c, ha⟩ : bcocycles L a)) =
      Submodule.Quotient.mk (⟨c, hb⟩ : bcocycles L b) := by
  subst b
  rfl

theorem onHR_w (q : ℕ) (x : HR K q) :
    castHR (Nat.add_assoc p q 1).symm (onHR A (q+1) (w K q x)) =
      w L (p+q) (onHR A q x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change castHR (Nat.add_assoc p q 1).symm
      (Submodule.Quotient.mk (⟨total A (c : Seq K), _⟩ : bcocycles L (p+(q+1)))) =
    Submodule.Quotient.mk (⟨total A (c : Seq K), _⟩ : bcocycles L (p+q+1))
  exact castHR_mk _ _ _ _

theorem total_natural {M N : InvComplex} (B : Map M N p)
    (φ : InvHom K M) (ψ : InvHom L N)
    (h : ∀ j x, ψ.f (p+j) (A.f j x) = B.f j (φ.f j x)) (c : Seq K) :
    seqMap ψ (total A c) = total B (seqMap φ c) := by
  funext j
  rw [seqMap_apply]
  by_cases hj : p ≤ j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [total_at, total_at, seqMap_apply, h]
  · rw [total_below A c (by omega), map_zero, total_below B (seqMap φ c) (by omega)]

theorem onHR_natural {M N : InvComplex} (B : Map M N p)
    (φ : InvHom K M) (ψ : InvHom L N)
    (h : ∀ j x, ψ.f (p+j) (A.f j x) = B.f j (φ.f j x)) (q : ℕ) (x : HR K q) :
    HRmap ψ (p+q) (onHR A q x) = onHR B q (HRmap φ q x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [onHR_mk, HRmap, Submodule.mapQ_apply, HRmap, Submodule.mapQ_apply, onHR_mk]
  congr 1
  apply Subtype.ext
  exact total_natural A B φ ψ h (c : Seq K)
end
end Finsler.BorelGraded
