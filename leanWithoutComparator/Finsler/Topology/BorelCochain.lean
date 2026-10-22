module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.Abel

/-! Borel cochains for an involution of an F₂-cochain complex. For cochain modules C j with
differentials d and a cochain involution t, the Borel cochains of total degree n are the
sequences (c j) supported in degrees ≤ n; the Borel differential is
(D c)₀ = (1 + t) c₀ and (D c)_{j+1} = d c_j + (1 + t) c_{j+1}. This is the total complex of the
cochains with the periodic F₂[C₂]-resolution (d = 1 + t), so its cohomology is the Borel
cohomology. The inclusion of Borel cochains of degree n into degree n + 1 is multiplication by
the generator w, projection to the degree-n component forgets the action, and the connecting map
of 0 → (degree ≤ n − 1) → (degree ≤ n) → C n → 0 is the transfer x ↦ (1 + t) x. The Gysin
sequence ⋯ → H_R^{n} →w→ H_R^{n+1} → H^{n+1} →(1+t)→ H_R^{n+1} → ⋯ is exact. -/

@[expose] public section

namespace Finsler.BorelCochain

noncomputable section

/-- An F₂-cochain complex with a cochain involution. -/
structure InvComplex where
  C : ℕ → Type
  [acg : ∀ j, AddCommGroup (C j)]
  [mod : ∀ j, Module (ZMod 2) (C j)]
  d : ∀ j, C j →ₗ[ZMod 2] C (j + 1)
  t : ∀ j, C j →ₗ[ZMod 2] C j
  dd : ∀ j x, d (j + 1) (d j x) = 0
  tt : ∀ j x, t j (t j x) = x
  td : ∀ j x, t (j + 1) (d j x) = d j (t j x)

attribute [instance] InvComplex.acg InvComplex.mod

variable (K : InvComplex)

theorem two_eq_zero_of_mod {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have h : (2 : ZMod 2) = 0 := rfl
  rw [h, zero_smul]

/-- The transfer 1 + t on cochains. -/
def tr (j : ℕ) : K.C j →ₗ[ZMod 2] K.C j := LinearMap.id + K.t j

theorem tr_apply (j : ℕ) (x : K.C j) : tr K j x = x + K.t j x := rfl

theorem tr_tr (j : ℕ) (x : K.C j) : tr K j (tr K j x) = 0 := by
  simp only [tr_apply, map_add, K.tt]
  calc x + K.t j x + (K.t j x + x) = (x + x) + (K.t j x + K.t j x) := by abel
    _ = 0 := by rw [two_eq_zero_of_mod, two_eq_zero_of_mod, add_zero]

theorem tr_d (j : ℕ) (x : K.C j) : tr K (j + 1) (K.d j x) = K.d j (tr K j x) := by
  simp only [tr_apply, map_add, K.td]

/-- Ordinary cocycles. -/
def cocycles (n : ℕ) : Submodule (ZMod 2) (K.C n) := LinearMap.ker (K.d n)

/-- Ordinary coboundaries. -/
def coboundaries : (n : ℕ) → Submodule (ZMod 2) (K.C n)
  | 0 => ⊥
  | m + 1 => LinearMap.range (K.d m)

theorem coboundaries_le (n : ℕ) : coboundaries K n ≤ cocycles K n := by
  cases n with
  | zero => exact bot_le
  | succ m =>
    rintro _ ⟨x, rfl⟩
    exact K.dd m x

/-- Ordinary cohomology. -/
abbrev H (n : ℕ) : Type :=
  cocycles K n ⧸ (coboundaries K n).comap (cocycles K n).subtype

/-- Total cochains: all sequences of cochains. -/
abbrev Seq : Type := (j : ℕ) → K.C j

/-- Sequences supported in degrees < k. -/
def low (k : ℕ) : Submodule (ZMod 2) (Seq K) where
  carrier := {c | ∀ j, k ≤ j → c j = 0}
  add_mem' := by
    intro a b ha hb j hj
    simp [ha j hj, hb j hj]
  zero_mem' := by
    intro j _
    rfl
  smul_mem' := by
    intro r a ha j hj
    simp [ha j hj]

theorem low_mono {k l : ℕ} (hkl : k ≤ l) : low K k ≤ low K l :=
  fun _ hc j hj => hc j (hkl.trans hj)

theorem mem_low_zero {c : Seq K} (hc : c ∈ low K 0) : c = 0 := by
  funext j
  exact hc j (Nat.zero_le j)

theorem single_ne {n j : ℕ} (h : j ≠ n) (y : K.C n) : (Pi.single n y : Seq K) j = 0 :=
  Pi.single_eq_of_ne h y

theorem single_same (n : ℕ) (y : K.C n) : (Pi.single n y : Seq K) n = y :=
  Pi.single_eq_same n y

theorem single_zero_seq (n : ℕ) : (Pi.single n (0 : K.C n) : Seq K) = 0 :=
  Pi.single_zero n

theorem single_mem_low (n : ℕ) (y : K.C n) : (Pi.single n y : Seq K) ∈ low K (n + 1) := by
  intro j hj
  exact single_ne K (show j ≠ n by omega) y

/-- The components of the Borel differential. -/
def DComp : (j : ℕ) → Seq K →ₗ[ZMod 2] K.C j
  | 0 => tr K 0 ∘ₗ LinearMap.proj 0
  | j + 1 => K.d j ∘ₗ LinearMap.proj j + tr K (j + 1) ∘ₗ LinearMap.proj (j + 1)

/-- The Borel differential. -/
def D : Seq K →ₗ[ZMod 2] Seq K := LinearMap.pi (DComp K)

theorem D_zero (c : Seq K) : D K c 0 = tr K 0 (c 0) := rfl

theorem D_succ (c : Seq K) (j : ℕ) : D K c (j + 1) = K.d j (c j) + tr K (j + 1) (c (j + 1)) :=
  rfl

theorem D_mem_low {k : ℕ} {c : Seq K} (hc : c ∈ low K k) : D K c ∈ low K (k + 1) := by
  intro j hj
  cases j with
  | zero => omega
  | succ j =>
    rw [D_succ, hc j (by omega), hc (j + 1) (by omega), map_zero, map_zero, add_zero]

theorem D_D (c : Seq K) : D K (D K c) = 0 := by
  funext j
  cases j with
  | zero =>
    change tr K 0 (tr K 0 (c 0)) = 0
    exact tr_tr K 0 (c 0)
  | succ j =>
    change K.d j (D K c j) + tr K (j + 1) (K.d j (c j) + tr K (j + 1) (c (j + 1))) = 0
    rw [map_add, tr_tr K, add_zero, tr_d K]
    cases j with
    | zero =>
      change K.d 0 (tr K 0 (c 0)) + K.d 0 (tr K 0 (c 0)) = 0
      exact two_eq_zero_of_mod _
    | succ i =>
      change K.d (i + 1) (K.d i (c i) + tr K (i + 1) (c (i + 1))) +
        K.d (i + 1) (tr K (i + 1) (c (i + 1))) = 0
      rw [map_add, K.dd, zero_add]
      exact two_eq_zero_of_mod _

/-- The Borel image of a lifted cochain. -/
theorem D_single (n : ℕ) (y : K.C n) :
    D K (Pi.single n y) = Pi.single n (tr K n y) + Pi.single (n + 1) (K.d n y) := by
  funext j
  rw [Pi.add_apply]
  cases j with
  | zero =>
    rw [D_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [single_same, single_same, single_ne K (show (0 : ℕ) ≠ 0 + 1 by omega), add_zero]
    · rw [single_ne K (show (0 : ℕ) ≠ n by omega), single_ne K (show (0 : ℕ) ≠ n by omega),
        single_ne K (show (0 : ℕ) ≠ n + 1 by omega), map_zero, add_zero]
  | succ i =>
    rw [D_succ]
    by_cases h1 : i + 1 = n
    · subst h1
      rw [single_ne K (show i ≠ i + 1 by omega), single_same, single_same,
        single_ne K (show i + 1 ≠ i + 1 + 1 by omega), map_zero, zero_add, add_zero]
    · by_cases h2 : i = n
      · subst h2
        rw [single_same, single_ne K (show i + 1 ≠ i by omega),
          single_ne K (show i + 1 ≠ i by omega), single_same, map_zero, add_zero, zero_add]
      · rw [single_ne K h2, single_ne K h1, single_ne K h1,
          single_ne K (show i + 1 ≠ n + 1 by omega), map_zero, map_zero, add_zero]

/-- Borel cocycles of degree n. -/
def bcocycles (n : ℕ) : Submodule (ZMod 2) (Seq K) := low K (n + 1) ⊓ LinearMap.ker (D K)

/-- Borel coboundaries of degree n. -/
def bcoboundaries (n : ℕ) : Submodule (ZMod 2) (Seq K) := (low K n).map (D K)

theorem mem_bcocycles {n : ℕ} {c : Seq K} :
    c ∈ bcocycles K n ↔ c ∈ low K (n + 1) ∧ D K c = 0 := Iff.rfl

theorem bcoboundaries_le (n : ℕ) : bcoboundaries K n ≤ bcocycles K n := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨D_mem_low K hb, D_D K b⟩

/-- Borel cohomology. -/
abbrev HR (n : ℕ) : Type :=
  bcocycles K n ⧸ (bcoboundaries K n).comap (bcocycles K n).subtype

theorem bcocycles_mono (n : ℕ) : bcocycles K n ≤ bcocycles K (n + 1) :=
  inf_le_inf_right _ (low_mono K (Nat.le_succ _))

theorem bcoboundaries_mono (n : ℕ) : bcoboundaries K n ≤ bcoboundaries K (n + 1) :=
  Submodule.map_mono (low_mono K (Nat.le_succ _))

/-- Multiplication by w: inclusion of Borel cochains. -/
def w (n : ℕ) : HR K n →ₗ[ZMod 2] HR K (n + 1) :=
  Submodule.mapQ _ _ (Submodule.inclusion (bcocycles_mono K n)) (by
    intro x hx
    exact bcoboundaries_mono K n hx)

theorem bcocycle_comp (n : ℕ) (c : bcocycles K n) : K.d n ((c : Seq K) n) = 0 := by
  have h1 : D K (c : Seq K) (n + 1) = 0 := by
    rw [((mem_bcocycles K).mp c.2).2]
    rfl
  rw [D_succ, ((mem_bcocycles K).mp c.2).1 (n + 1) le_rfl, map_zero, add_zero] at h1
  exact h1

/-- The degree-n component of a Borel cocycle is an ordinary cocycle. -/
def forgetCocycle (n : ℕ) : bcocycles K n →ₗ[ZMod 2] cocycles K n where
  toFun c := ⟨(c : Seq K) n, bcocycle_comp K n c⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem forgetCocycle_coboundary (n : ℕ) :
    (bcoboundaries K n).comap (bcocycles K n).subtype ≤
      ((coboundaries K n).comap (cocycles K n).subtype).comap (forgetCocycle K n) := by
  rintro c ⟨b, hb, hbc⟩
  have hbc' : D K b = (c : Seq K) := hbc
  change (c : Seq K) n ∈ coboundaries K n
  rw [← hbc']
  cases n with
  | zero =>
    rw [D_zero, mem_low_zero K hb]
    change tr K 0 0 ∈ coboundaries K 0
    rw [map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    rw [D_succ, hb (m + 1) le_rfl, map_zero, add_zero]
    exact ⟨b m, rfl⟩

/-- Forgetting the action. -/
def forget (n : ℕ) : HR K n →ₗ[ZMod 2] H K n :=
  Submodule.mapQ _ _ (forgetCocycle K n) (forgetCocycle_coboundary K n)

theorem trSingle_cocycle (n : ℕ) (x : cocycles K n) :
    D K (Pi.single n (tr K n (x : K.C n))) = 0 := by
  have hx : K.d n (x : K.C n) = 0 := x.2
  rw [D_single, tr_tr K, ← tr_d K, hx, map_zero, single_zero_seq K, single_zero_seq K, add_zero]

/-- The Borel cocycle of a transfer. -/
def trCocycle (n : ℕ) : cocycles K n →ₗ[ZMod 2] bcocycles K n :=
  LinearMap.codRestrict (bcocycles K n)
    (LinearMap.single (ZMod 2) K.C n ∘ₗ tr K n ∘ₗ (cocycles K n).subtype)
    (fun x => ⟨single_mem_low K n _, trSingle_cocycle K n x⟩)

theorem trCocycle_coe (n : ℕ) (x : cocycles K n) :
    (trCocycle K n x : Seq K) = Pi.single n (tr K n (x : K.C n)) := rfl

theorem trCocycle_coboundary (n : ℕ) :
    (coboundaries K n).comap (cocycles K n).subtype ≤
      ((bcoboundaries K n).comap (bcocycles K n).subtype).comap (trCocycle K n) := by
  intro x hx
  change Pi.single n (tr K n (x : K.C n)) ∈ bcoboundaries K n
  cases n with
  | zero =>
    have h0 : (x : K.C 0) = 0 := (Submodule.mem_bot (ZMod 2)).mp hx
    rw [h0, map_zero, single_zero_seq K]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨z, hz⟩ := hx
    refine ⟨Pi.single m (tr K m z), single_mem_low K m _, ?_⟩
    rw [D_single, tr_tr K, single_zero_seq K, zero_add, ← tr_d K]
    change Pi.single (m + 1) (tr K (m + 1) (K.d m z)) = Pi.single (m + 1) (tr K (m + 1) _)
    rw [hz]
    rfl

/-- The transfer x ↦ (1 + t) x, the connecting map of the Gysin sequence. -/
def transfer (n : ℕ) : H K n →ₗ[ZMod 2] HR K n :=
  Submodule.mapQ _ _ (trCocycle K n) (trCocycle_coboundary K n)

theorem mk_eq_zero_iff_bcoboundary (n : ℕ) (c : bcocycles K n) :
    (Submodule.Quotient.mk c : HR K n) = 0 ↔ (c : Seq K) ∈ bcoboundaries K n :=
  Submodule.Quotient.mk_eq_zero _

theorem mk_eq_zero_iff_coboundary (n : ℕ) (x : cocycles K n) :
    (Submodule.Quotient.mk x : H K n) = 0 ↔ (x : K.C n) ∈ coboundaries K n :=
  Submodule.Quotient.mk_eq_zero _

/-- Exactness at H_R^{n+1}: kernel of forget = image of w. -/
theorem exact_forget (n : ℕ) (x : HR K (n + 1)) :
    forget K (n + 1) x = 0 ↔ ∃ y : HR K n, w K n y = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro h
    rw [forget, Submodule.mapQ_apply, mk_eq_zero_iff_coboundary] at h
    obtain ⟨y, hy⟩ := h
    have hy' : K.d n y = (c : Seq K) (n + 1) := hy
    set c' : Seq K := (c : Seq K) - D K (Pi.single n y) with hc'
    have hc'low : c' ∈ low K (n + 1) := by
      intro j hj
      rw [hc', Pi.sub_apply, D_single, Pi.add_apply]
      rcases Nat.lt_or_ge (n + 1) j with h' | h'
      · rw [((mem_bcocycles K).mp c.2).1 j (by omega), single_ne K (show j ≠ n by omega),
          single_ne K (show j ≠ n + 1 by omega), add_zero, sub_zero]
      · have hj' : j = n + 1 := by omega
        subst hj'
        rw [single_ne K (show n + 1 ≠ n by omega), single_same, zero_add, hy', sub_self]
    have hc'cocycle : c' ∈ bcocycles K n := by
      refine ⟨hc'low, ?_⟩
      change D K c' = 0
      rw [hc', map_sub, D_D, sub_zero]
      exact ((mem_bcocycles K).mp c.2).2
    refine ⟨Submodule.Quotient.mk ⟨c', hc'cocycle⟩, ?_⟩
    rw [w, Submodule.mapQ_apply, Submodule.Quotient.eq]
    change (c' - (c : Seq K)) ∈ bcoboundaries K (n + 1)
    refine ⟨-Pi.single n y, ?_, ?_⟩
    · exact Submodule.neg_mem _ (single_mem_low K n y)
    · rw [map_neg, hc']
      abel
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [w, Submodule.mapQ_apply, forget, Submodule.mapQ_apply, mk_eq_zero_iff_coboundary]
    change (b : Seq K) (n + 1) ∈ coboundaries K (n + 1)
    rw [((mem_bcocycles K).mp b.2).1 (n + 1) le_rfl]
    exact Submodule.zero_mem _

/-- Exactness at H_R^n between transfer and w: kernel of w = image of transfer. -/
theorem exact_w (n : ℕ) (y : HR K n) :
    w K n y = 0 ↔ ∃ z : H K n, transfer K n z = y := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  constructor
  · intro h
    rw [w, Submodule.mapQ_apply, mk_eq_zero_iff_bcoboundary] at h
    obtain ⟨b, hb, hbc⟩ := h
    have hbc' : D K b = (c : Seq K) := hbc
    have hx : K.d n (b n) = 0 := by
      have h1 : D K b (n + 1) = (c : Seq K) (n + 1) := by rw [hbc']
      rw [D_succ, hb (n + 1) le_rfl, map_zero, add_zero,
        ((mem_bcocycles K).mp c.2).1 (n + 1) le_rfl] at h1
      exact h1
    refine ⟨Submodule.Quotient.mk ⟨b n, hx⟩, ?_⟩
    rw [transfer, Submodule.mapQ_apply, Submodule.Quotient.eq]
    change Pi.single n (tr K n (b n)) - (c : Seq K) ∈ bcoboundaries K n
    refine ⟨Pi.single n (b n) - b, ?_, ?_⟩
    · intro j hj
      rw [Pi.sub_apply]
      rcases Nat.lt_or_ge n j with h' | h'
      · rw [single_ne K (show j ≠ n by omega), hb j (by omega), sub_zero]
      · have hj' : j = n := by omega
        subst hj'
        rw [single_same, sub_self]
    · rw [map_sub, D_single, hx, single_zero_seq K, add_zero, hbc']
  · rintro ⟨z, hz⟩
    rw [← hz]
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [transfer, Submodule.mapQ_apply, w, Submodule.mapQ_apply, mk_eq_zero_iff_bcoboundary]
    change Pi.single n (tr K n (x : K.C n)) ∈ bcoboundaries K (n + 1)
    refine ⟨Pi.single n x, single_mem_low K n _, ?_⟩
    have hx : K.d n (x : K.C n) = 0 := x.2
    rw [D_single, hx, single_zero_seq K, add_zero]

/-- Exactness at H^n between forget and transfer: kernel of transfer = image of forget. -/
theorem exact_transfer (n : ℕ) (z : H K n) :
    transfer K n z = 0 ↔ ∃ y : HR K n, forget K n y = z := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  constructor
  · intro h
    rw [transfer, Submodule.mapQ_apply, mk_eq_zero_iff_bcoboundary] at h
    obtain ⟨b, hb, hbc⟩ := h
    have hbc' : D K b = Pi.single n (tr K n (x : K.C n)) := hbc
    have hx : K.d n (x : K.C n) = 0 := x.2
    set c : Seq K := Pi.single n (x : K.C n) - b with hc
    have hclow : c ∈ low K (n + 1) := by
      intro j hj
      rw [hc, Pi.sub_apply, single_ne K (show j ≠ n by omega), hb j (by omega), sub_zero]
    have hcD : D K c = 0 := by
      rw [hc, map_sub, D_single, hx, single_zero_seq K, add_zero, hbc', sub_self]
    refine ⟨Submodule.Quotient.mk ⟨c, hclow, hcD⟩, ?_⟩
    rw [forget, Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    change c n = (x : K.C n)
    rw [hc, Pi.sub_apply, single_same, hb n le_rfl, sub_zero]
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [forget, Submodule.mapQ_apply, transfer, Submodule.mapQ_apply,
      mk_eq_zero_iff_bcoboundary]
    change Pi.single n (tr K n ((c : Seq K) n)) ∈ bcoboundaries K n
    refine ⟨Pi.single n ((c : Seq K) n) - (c : Seq K), ?_, ?_⟩
    · intro j hj
      rw [Pi.sub_apply]
      rcases Nat.lt_or_ge n j with h' | h'
      · rw [single_ne K (show j ≠ n by omega), ((mem_bcocycles K).mp c.2).1 j (by omega),
          sub_zero]
      · have hj' : j = n := by omega
        subst hj'
        rw [single_same, sub_self]
    · rw [map_sub, D_single, ((mem_bcocycles K).mp c.2).2, sub_zero, bcocycle_comp K n c,
        single_zero_seq K, add_zero]

section Naturality

/-- Equivariant cochain maps. -/
structure InvHom (K L : InvComplex) where
  f : ∀ j, K.C j →ₗ[ZMod 2] L.C j
  comm_d : ∀ j x, f (j + 1) (K.d j x) = L.d j (f j x)
  comm_t : ∀ j x, f j (K.t j x) = L.t j (f j x)

variable {K} {L M : InvComplex} (φ : InvHom K L) (ψ : InvHom L M)

theorem comm_tr (j : ℕ) (x : K.C j) : φ.f j (tr K j x) = tr L j (φ.f j x) := by
  rw [tr_apply, tr_apply, map_add, φ.comm_t]

/-- The induced map on total cochains. -/
def seqMap : Seq K →ₗ[ZMod 2] Seq L := LinearMap.pi fun j => φ.f j ∘ₗ LinearMap.proj j

theorem seqMap_apply (c : Seq K) (j : ℕ) : seqMap φ c j = φ.f j (c j) := rfl

theorem seqMap_D (c : Seq K) : seqMap φ (D K c) = D L (seqMap φ c) := by
  funext j
  cases j with
  | zero =>
    rw [seqMap_apply, D_zero, D_zero, comm_tr]
    rfl
  | succ j =>
    rw [seqMap_apply, D_succ, D_succ, map_add, φ.comm_d, comm_tr]
    rfl

theorem seqMap_low {k : ℕ} {c : Seq K} (hc : c ∈ low K k) : seqMap φ c ∈ low L k := by
  intro j hj
  rw [seqMap_apply, hc j hj, map_zero]

theorem seqMap_single (n : ℕ) (y : K.C n) :
    seqMap φ (Pi.single n y) = Pi.single n (φ.f n y) := by
  funext j
  rw [seqMap_apply]
  by_cases h : j = n
  · subst h
    rw [single_same, single_same]
  · rw [single_ne K h, single_ne L h, map_zero]

/-- The induced map on Borel cocycles. -/
def bcocycleMap (n : ℕ) : bcocycles K n →ₗ[ZMod 2] bcocycles L n :=
  LinearMap.codRestrict (bcocycles L n) (seqMap φ ∘ₗ (bcocycles K n).subtype) (fun c =>
    ⟨seqMap_low φ ((mem_bcocycles K).mp c.2).1, by
      change D L (seqMap φ (c : Seq K)) = 0
      rw [← seqMap_D, ((mem_bcocycles K).mp c.2).2, map_zero]⟩)

theorem bcocycleMap_coboundary (n : ℕ) :
    (bcoboundaries K n).comap (bcocycles K n).subtype ≤
      ((bcoboundaries L n).comap (bcocycles L n).subtype).comap (bcocycleMap φ n) := by
  rintro c ⟨b, hb, hbc⟩
  refine ⟨seqMap φ b, seqMap_low φ hb, ?_⟩
  change D L (seqMap φ b) = seqMap φ (c : Seq K)
  rw [← seqMap_D]
  exact congrArg (seqMap φ) hbc

/-- The induced map on Borel cohomology. -/
def HRmap (n : ℕ) : HR K n →ₗ[ZMod 2] HR L n :=
  Submodule.mapQ _ _ (bcocycleMap φ n) (bcocycleMap_coboundary φ n)

/-- The induced map on cocycles. -/
def cocycleMap (n : ℕ) : cocycles K n →ₗ[ZMod 2] cocycles L n :=
  LinearMap.codRestrict (cocycles L n) (φ.f n ∘ₗ (cocycles K n).subtype) (fun x => by
    change L.d n (φ.f n (x : K.C n)) = 0
    rw [← φ.comm_d]
    have hx : K.d n (x : K.C n) = 0 := x.2
    rw [hx, map_zero])

theorem cocycleMap_coboundary (n : ℕ) :
    (coboundaries K n).comap (cocycles K n).subtype ≤
      ((coboundaries L n).comap (cocycles L n).subtype).comap (cocycleMap φ n) := by
  intro x hx
  change φ.f n (x : K.C n) ∈ coboundaries L n
  cases n with
  | zero =>
    have h0 : (x : K.C 0) = 0 := (Submodule.mem_bot (ZMod 2)).mp hx
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨z, hz⟩ := hx
    refine ⟨φ.f m z, ?_⟩
    rw [← φ.comm_d]
    exact congrArg (φ.f (m + 1)) hz

/-- The induced map on ordinary cohomology. -/
def Hmap (n : ℕ) : H K n →ₗ[ZMod 2] H L n :=
  Submodule.mapQ _ _ (cocycleMap φ n) (cocycleMap_coboundary φ n)

theorem HRmap_w (n : ℕ) (y : HR K n) : HRmap φ (n + 1) (w K n y) = w L n (HRmap φ n y) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem Hmap_forget (n : ℕ) (y : HR K n) :
    Hmap φ n (forget K n y) = forget L n (HRmap φ n y) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem HRmap_transfer (n : ℕ) (z : H K n) :
    HRmap φ n (transfer K n z) = transfer L n (Hmap φ n z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [transfer, Submodule.mapQ_apply, HRmap, Submodule.mapQ_apply, Hmap, Submodule.mapQ_apply,
    transfer, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change seqMap φ (Pi.single n (tr K n (x : K.C n))) = Pi.single n (tr L n (φ.f n (x : K.C n)))
  rw [seqMap_single, comm_tr]

/-- Composition of equivariant cochain maps. -/
def invHomComp : InvHom K M where
  f j := ψ.f j ∘ₗ φ.f j
  comm_d j x := by
    change ψ.f (j + 1) (φ.f (j + 1) (K.d j x)) = M.d j (ψ.f j (φ.f j x))
    rw [φ.comm_d, ψ.comm_d]
  comm_t j x := by
    change ψ.f j (φ.f j (K.t j x)) = M.t j (ψ.f j (φ.f j x))
    rw [φ.comm_t, ψ.comm_t]

theorem HRmap_comp (n : ℕ) (y : HR K n) :
    HRmap (invHomComp φ ψ) n y = HRmap ψ n (HRmap φ n y) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem Hmap_comp (n : ℕ) (z : H K n) :
    Hmap (invHomComp φ ψ) n z = Hmap ψ n (Hmap φ n z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

end Naturality

end

end Finsler.BorelCochain
