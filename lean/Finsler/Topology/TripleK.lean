module

public import Finsler.Topology.OperatorK

/-! The Borel sequence of a short exact sequence of complexes with two commuting involutions, and
high-degree localization. The connecting map of the Borel long exact sequence commutes with
degree-raising cochain maps compatible with the sequence; in particular, for iterated Borel
complexes, with the reflection class. For three graded modules G′ → G and G″ → G′ (of degree
one) which are exact at G′, with commuting degree-one operators, powers of the operator
vanishing on G and on G″ give a power vanishing on G′; hence a power of the reflection class
vanishing on the iterated Borel cohomology of the middle and of the quotient complex gives one
on that of the subcomplex. If the reflection Borel cohomology of the middle and of the quotient
complex vanishes from some degree on, so does that of the subcomplex. If moreover a power of
U = v(v + w) vanishes on the iterated Borel cohomology of the subcomplex, a power of v vanishes
there; since v is injective above the degrees of the reflection Borel cohomology, the iterated
Borel cohomology of the subcomplex vanishes in high degrees, and the map from the middle to the
quotient complex is bijective on iterated Borel cohomology in high degrees. -/

@[expose] public section

namespace Finsler.TripleK

open Finsler.BorelCochain Finsler.BorelIterate Finsler.BorelGraded Finsler.BorelFreeK
open Finsler.BorelExact Finsler.BorelCoverK Finsler.NilpotentWK Finsler.OperatorK

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### The connecting map and degree-raising maps -/

section Graded

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

/-- The connecting map commutes with the change of degree along an equality. -/
theorem delta_castHR {a b : ℕ} (hab : a = b) (x : HR K'' a) :
    delta h b (castHR hab x) = castHR (congrArg (· + 1) hab) (delta h a x) := by
  subst b
  rfl

/-- The connecting map commutes with degree-raising cochain maps compatible with the two maps of
the sequence. -/
theorem delta_onHR {p : ℕ} (A' : Map K' K' p) (A : Map K K p) (A'' : Map K'' K'' p)
    (hl : ∀ j z, ι.f (p + j) (A'.f j z) = A.f j (ι.f j z))
    (hr : ∀ j x, π.f (p + j) (A.f j x) = A''.f j (π.f j x)) (n : ℕ) (x : HR K'' n) :
    delta h (p + n) (onHR A'' n x) =
      castHR (Nat.add_assoc p n 1).symm (onHR A' (n + 1) (delta h n x)) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  rw [delta_mk h n c b hb hπb ⟨z, hz⟩ hιz, onHR_mk, onHR_mk]
  have hzc : total A' z ∈ bcocycles K' (p + n + 1) := (cyclesMap A' (n + 1) ⟨z, hz⟩).2
  have hlow : total A b ∈ low K (p + n + 1) := total_low A hb
  have e : castHR (Nat.add_assoc p n 1).symm
      (Submodule.Quotient.mk (cyclesMap A' (n + 1) ⟨z, hz⟩)) =
      Submodule.Quotient.mk (⟨total A' z, hzc⟩ : bcocycles K' (p + n + 1)) :=
    castHR_mk (Nat.add_assoc p n 1).symm (total A' z) (cyclesMap A' (n + 1) ⟨z, hz⟩).2 hzc
  rw [e]
  refine delta_mk h (p + n) (cyclesMap A'' n c) (total A b) hlow ?_ ⟨total A' z, hzc⟩ ?_
  · change seqMap π (total A b) = total A'' (c : Seq K'')
    rw [total_natural A A'' π π hr b, hπb]
  · change seqMap ι (total A' z) = D K (total A b)
    rw [total_natural A' A ι ι hl z, hιz, total_D]

end Graded

/-! ### Three graded modules -/

section Families

variable {G' G G'' : ℕ → Type} [∀ q, AddCommGroup (G' q)] [∀ q, Module (ZMod 2) (G' q)]
  [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
  [∀ q, AddCommGroup (G'' q)] [∀ q, Module (ZMod 2) (G'' q)]

/-- A degreewise family of maps as a map of the products of the graded pieces. -/
def piMap (i : ∀ q, G' q →ₗ[ZMod 2] G q) : ((q : ℕ) → G' q) →ₗ[ZMod 2] ((q : ℕ) → G q) :=
  LinearMap.pi fun q => i q ∘ₗ LinearMap.proj q

/-- A family of degree-one maps between two graded modules as a map of the products of the
graded pieces. -/
def shiftMap (d : ∀ q, G'' q →ₗ[ZMod 2] G' (q + 1)) :
    ((q : ℕ) → G'' q) →ₗ[ZMod 2] ((q : ℕ) → G' q) where
  toFun x j := Nat.casesOn (motive := G') j 0 fun q => d q (x q)
  map_add' x y := by
    funext j
    cases j with
    | zero => exact (add_zero (0 : G' 0)).symm
    | succ q => exact map_add (d q) (x q) (y q)
  map_smul' c x := by
    funext j
    cases j with
    | zero => exact (smul_zero c).symm
    | succ q => exact map_smul (d q) c (x q)

variable (i : ∀ q, G' q →ₗ[ZMod 2] G q) (d : ∀ q, G'' q →ₗ[ZMod 2] G' (q + 1))
  (f' : ∀ q, G' q →ₗ[ZMod 2] G' (q + 1)) (f : ∀ q, G q →ₗ[ZMod 2] G (q + 1))
  (f'' : ∀ q, G'' q →ₗ[ZMod 2] G'' (q + 1))

theorem piMap_shiftOp (hi : ∀ q y, i (q + 1) (f' q y) = f q (i q y)) (y : (q : ℕ) → G' q) :
    piMap i (shiftOp G' f' y) = shiftOp G f (piMap i y) := by
  funext j
  cases j with
  | zero => exact map_zero (i 0)
  | succ q => exact hi q (y q)

theorem piMap_pow (hi : ∀ q y, i (q + 1) (f' q y) = f q (i q y)) (k : ℕ)
    (y : (q : ℕ) → G' q) :
    piMap i ((shiftOp G' f' ^ k) y) = (shiftOp G f ^ k) (piMap i y) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    change piMap i (shiftOp G' f' ((shiftOp G' f' ^ k) y)) =
      shiftOp G f ((shiftOp G f ^ k) (piMap i y))
    rw [piMap_shiftOp i f' f hi, ih]

theorem shiftOp_shiftMap (hd : ∀ q x, f' (q + 1) (d q x) = d (q + 1) (f'' q x))
    (x : (q : ℕ) → G'' q) :
    shiftOp G' f' (shiftMap d x) = shiftMap d (shiftOp G'' f'' x) := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero =>
      change f' 0 (0 : G' 0) = d 0 (0 : G'' 0)
      rw [map_zero, map_zero]
    | succ q => exact hd q (x q)

theorem shiftOp_pow_shiftMap (hd : ∀ q x, f' (q + 1) (d q x) = d (q + 1) (f'' q x)) (k : ℕ)
    (x : (q : ℕ) → G'' q) :
    (shiftOp G' f' ^ k) (shiftMap d x) = shiftMap d ((shiftOp G'' f'' ^ k) x) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    change shiftOp G' f' ((shiftOp G' f' ^ k) (shiftMap d x)) =
      shiftMap d (shiftOp G'' f'' ((shiftOp G'' f'' ^ k) x))
    rw [ih, shiftOp_shiftMap d f' f'' hd]

/-- Exactness at the middle module, on the products of the graded pieces. -/
theorem exists_shiftMap_eq (hinj : Function.Injective (i 0))
    (hex : ∀ q (y : G' (q + 1)), i (q + 1) y = 0 → ∃ x : G'' q, d q x = y)
    (y : (q : ℕ) → G' q) (hy : piMap i y = 0) : ∃ x : (q : ℕ) → G'' q, shiftMap d x = y := by
  have h : ∀ q, ∃ x : G'' q, d q x = y (q + 1) := fun q =>
    hex q (y (q + 1)) (congrFun hy (q + 1))
  choose x hx using h
  refine ⟨x, ?_⟩
  funext j
  cases j with
  | zero =>
    have h0 : i 0 (y 0) = i 0 0 := by
      rw [map_zero]
      exact congrFun hy 0
    exact (hinj h0).symm
  | succ q => exact hx q

/-- For graded modules G′ → G and G″ → G′ (of degree one), exact at G′, with commuting
degree-one operators: if the M₁-fold composites vanish on G and the M₂-fold composites vanish on
G″, the (M₂ + M₁)-fold composites vanish on G′. -/
theorem word_sub_nilpotent (hi : ∀ q y, i (q + 1) (f' q y) = f q (i q y))
    (hd : ∀ q x, f' (q + 1) (d q x) = d (q + 1) (f'' q x))
    (hinj : Function.Injective (i 0))
    (hex : ∀ q (y : G' (q + 1)), i (q + 1) y = 0 → ∃ x : G'' q, d q x = y) {M₁ M₂ : ℕ}
    (hf : ∀ (lo : ℕ) (x : G lo), Finsler.Gysin.word (V := fun j => G (lo + j))
      (fun j => (f (lo + j)).toAddMonoidHom) M₁ x = 0)
    (hf'' : ∀ (lo : ℕ) (x : G'' lo), Finsler.Gysin.word (V := fun j => G'' (lo + j))
      (fun j => (f'' (lo + j)).toAddMonoidHom) M₂ x = 0) (lo : ℕ) (y : G' lo) :
    Finsler.Gysin.word (V := fun j => G' (lo + j)) (fun j => (f' (lo + j)).toAddMonoidHom)
      (M₂ + M₁) y = 0 := by
  apply word_eq_zero_of_pow f' (M₂ + M₁)
  apply LinearMap.ext
  intro z
  rw [pow_add]
  change (shiftOp G' f' ^ M₂) ((shiftOp G' f' ^ M₁) z) = 0
  have h1 : piMap i ((shiftOp G' f' ^ M₁) z) = 0 := by
    rw [piMap_pow i f' f hi, shiftOp_pow_eq_zero f M₁ hf]
    rfl
  obtain ⟨x, hx⟩ := exists_shiftMap_eq i d hinj hex _ h1
  rw [← hx, shiftOp_pow_shiftMap d f' f'' hd, shiftOp_pow_eq_zero f'' M₂ hf'',
    LinearMap.zero_apply, map_zero]

end Families

/-! ### Short exact sequences of involutive complexes -/

section Localization

variable {L' L L'' : InvComplex} {ι : InvHom L' L} {π : InvHom L L''} (h : ShortExact ι π)

include h in
/-- If the Borel cohomology of the middle complex vanishes in degree n + 1 and that of the
quotient complex in degree n, that of the subcomplex vanishes in degree n + 1. -/
theorem HR_sub_eq_zero (n : ℕ) (hL : ∀ x : HR L (n + 1), x = 0) (hL'' : ∀ x : HR L'' n, x = 0)
    (y : HR L' (n + 1)) : y = 0 := by
  obtain ⟨x, rfl⟩ := exact_sub h n y (hL _)
  rw [hL'' x, map_zero]

include h in
/-- If the Borel cohomology of the subcomplex vanishes in degrees q and q + 1, the map to the
quotient complex is bijective on Borel cohomology of degree q. -/
theorem bijective_of_sub_zero (q : ℕ) (h0 : ∀ y : HR L' q, y = 0)
    (h1 : ∀ y : HR L' (q + 1), y = 0) : Function.Bijective (HRmap π q) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := exact_mid h q x hx
    rw [h0 z, map_zero]
  · intro c
    exact exact_delta h q c (h1 _)

end Localization

theorem word_injective {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] (f : ∀ n, V n →+ V (n + 1))
    (hf : ∀ n, Function.Injective (f n)) (k : ℕ) :
    Function.Injective (Finsler.Gysin.word f k) := by
  induction k with
  | zero => exact fun _ _ hxy => hxy
  | succ k ih => exact fun x y hxy => ih (hf k hxy)

/-- If ordinary cohomology vanishes from degree Q on and some power of w vanishes, Borel
cohomology vanishes from degree Q on: there w is injective. -/
theorem HR_eq_zero_of_word (L : InvComplex) {Q N : ℕ}
    (hzero : ∀ q, Q ≤ q → ∀ z : H L q, z = 0)
    (hnil : ∀ (lo : ℕ) (x : HR L lo), Finsler.Gysin.word (V := fun i => HR L (lo + i))
      (fun i => (w L (lo + i)).toAddMonoidHom) N x = 0) (q : ℕ) (hq : Q ≤ q) (x : HR L q) :
    x = 0 := by
  have hinj : ∀ i, Function.Injective (w L (q + i)).toAddMonoidHom := fun i => by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (exact_w L (q + i) y).mp hy
    rw [hzero (q + i) (by omega) z, map_zero]
  exact word_injective (V := fun i => HR L (q + i)) (fun i => (w L (q + i)).toAddMonoidHom)
    hinj N ((hnil q x).trans (hnil q 0).symm)

/-! ### Iterated Borel complexes -/

section Iterated

variable {K' K K'' : InvComplex} {S' : Commuting K'} {S : Commuting K} {S'' : Commuting K''}
  (I : CommHom S' S) (P : CommHom S S'') (h : ShortExact I.φ P.φ)

/-- The connecting map of the iterated Borel sequence commutes with the reflection class. -/
theorem delta_innerStep (q : ℕ) (x : HR (borelInv S'') q) :
    delta (BorelQuasiIso.shortExact_iterated I P h) (q + 1) (innerStep S'' q x) =
      innerStep S' (q + 1) (delta (BorelQuasiIso.shortExact_iterated I P h) q x) := by
  rw [innerStep_apply, innerStep_apply, delta_castHR,
    delta_onHR (BorelQuasiIso.shortExact_iterated I P h) (innerW S') (innerW S) (innerW S'')
      (fun j z => seqOf_injective S _ rfl) (fun j y => seqOf_injective S'' _ rfl) q x,
    castHR_castHR]

include h in
/-- If a power of the reflection class vanishes on the Borel cohomology of the middle and of the
quotient iterated complex of a short exact sequence, a power vanishes on that of the
subcomplex. -/
theorem innerPow_sub_nilpotent {M₁ M₂ : ℕ}
    (hW : ∀ (lo : ℕ) (x : HR (borelInv S) lo), innerPow S lo M₁ x = 0)
    (hW'' : ∀ (lo : ℕ) (x : HR (borelInv S'') lo), innerPow S'' lo M₂ x = 0) (lo : ℕ)
    (y : HR (borelInv S') lo) : innerPow S' lo (M₂ + M₁) y = 0 := by
  have hW2 : ∀ (lo : ℕ) (x : HR (borelInv S) lo),
      Finsler.Gysin.word (V := fun j => HR (borelInv S) (lo + j))
        (fun j => (innerStep S (lo + j)).toAddMonoidHom) M₁ x = 0 := hW
  have hW2'' : ∀ (lo : ℕ) (x : HR (borelInv S'') lo),
      Finsler.Gysin.word (V := fun j => HR (borelInv S'') (lo + j))
        (fun j => (innerStep S'' (lo + j)).toAddMonoidHom) M₂ x = 0 := hW''
  exact word_sub_nilpotent (G' := fun q => HR (borelInv S') q)
    (G := fun q => HR (borelInv S) q) (G'' := fun q => HR (borelInv S'') q)
    (i := fun q => HRmap (borelHom I) q)
    (d := fun q => delta (BorelQuasiIso.shortExact_iterated I P h) q)
    (f' := fun q => innerStep S' q) (f := fun q => innerStep S q)
    (f'' := fun q => innerStep S'' q)
    (fun q y => HRmap_innerStep I q y)
    (fun q x => (delta_innerStep I P h q x).symm)
    (injective_zero (BorelQuasiIso.shortExact_iterated I P h))
    (fun q y hy => exact_sub (BorelQuasiIso.shortExact_iterated I P h) q y hy) hW2 hW2'' lo y

variable {Q M₁ M₂ k : ℕ}
  (hK : ∀ q, Q ≤ q → ∀ x : HR K q, x = 0) (hK'' : ∀ q, Q ≤ q → ∀ x : HR K'' q, x = 0)
  (hW : ∀ (lo : ℕ) (x : HR (borelInv S) lo), innerPow S lo M₁ x = 0)
  (hW'' : ∀ (lo : ℕ) (x : HR (borelInv S'') lo), innerPow S'' lo M₂ x = 0)
  (hU : ∀ (q : ℕ) (x : HR (borelInv S') q), Ann S' k q x)

include h hK hK'' hW hW'' hU in
/-- High-degree vanishing for the subcomplex: if the reflection Borel cohomology of the middle
and of the quotient complex vanishes from degree Q on, powers of the reflection class vanish on
their iterated Borel cohomology, and a power of U = v(v + w) vanishes on the iterated Borel
cohomology of the subcomplex, then the iterated Borel cohomology of the subcomplex vanishes from
degree Q + 1 on. -/
theorem HR_sub_eq_zero_of_nilpotent (q : ℕ) (hq : Q + 1 ≤ q) (y : HR (borelInv S') q) :
    y = 0 := by
  have hK' : ∀ q, Q + 1 ≤ q → ∀ y : HR K' q, y = 0 := by
    intro q hq y
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    exact HR_sub_eq_zero h m (hK (m + 1) (by omega)) (hK'' m (by omega)) y
  have hzero : ∀ q, Q + 1 ≤ q → ∀ z : H (borelInv S') q, z = 0 := by
    intro q hq z
    apply (cohomologyEquiv S' q).injective
    rw [hK' q hq (cohomologyEquiv S' q z), map_zero]
  exact HR_eq_zero_of_word (borelInv S') hzero
    (v_nilpotent S' (innerPow_sub_nilpotent I P h hW hW'') hU) q hq y

include h hK hK'' hW hW'' hU in
/-- High-degree localization: under the same hypotheses the map from the middle to the quotient
complex is bijective on iterated Borel cohomology from degree Q + 1 on. -/
theorem bijective_of_nilpotent (q : ℕ) (hq : Q + 1 ≤ q) :
    Function.Bijective (HRmap (borelHom P) q) :=
  bijective_of_sub_zero (BorelQuasiIso.shortExact_iterated I P h) q
    (HR_sub_eq_zero_of_nilpotent I P h hK hK'' hW hW'' hU q hq)
    (HR_sub_eq_zero_of_nilpotent I P h hK hK'' hW hW'' hU (q + 1) (by omega))

end Iterated

end

end Finsler.TripleK
