module

public import Finsler.Topology.GlobalBasis
public import Finsler.Topology.BasisBudget
public import Finsler.Topology.TorsionK

/-! Global K-lifts of the bottom and top classes.

The K-Borel cohomology of a pair with the reversal and the half rotation is the Borel cohomology
of the iterated complex (`borelInv`); forgetting the half rotation is `fgtR`. Algebra:

* `fgtR` intertwines the reflection class of the iterated complex with w, and kills the class v of
  the half rotation;
* `fgtR` commutes with the connecting maps of short exact sequences;
* in the lowest degree of a complex whose Borel cohomology vanishes below and has dimension at
  most one there, every Borel class lifts to the iterated complex (the Gysin sequence of the
  iterated complex in its lowest degree);
* a class killed by a power of v is annihilated by the same power of U = v(v + w).

A K-filtration is a global filtration (`GlobalBasis.RGlobal`) whose complexes carry commuting
half rotations, compatible with all maps, with two local inputs at the crossings: v^{d+2} = 0 on
the K-Borel cohomology of the crossings of even index (the half rotation acts freely there, and
n + 1 functionals odd under it and even under the reversal cover a neighbourhood of the critical
manifold), and for odd index a K-class of degree d + 1 + l_j lifting e τ_j (the K-invariant
evaluation (u(0) + u(1/2))/|u(0) + u(1/2)| near the critical manifold).

Then: every global bottom class X_j lifts to a global K-class ζ_j; for even j, U^{d+2} ζ_j = 0;
for odd j, e X_j lifts to a global K-class. The extensions from the stage j + 1 to the whole
space use the vanishing of the K-Borel cohomology of the tails below the next index; in the
boundary degree the connecting obstruction is detected by forgetting the half rotation, where it
is the reflection obstruction of a restriction of a global class, which vanishes. -/

@[expose] public section

namespace Finsler.GlobalK

open Finsler.BorelCochain Finsler.BorelExact Finsler.BorelIterate Finsler.BorelFreeK
open Finsler.BorelGraded Finsler.BasisBudget Finsler.BorelCoverK Finsler.CrossingCollapse
open Finsler.GysinPattern Finsler.FiltrationCollapse Finsler.GlobalBasis Module

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### Forgetting the half rotation -/

section Forget

variable {K : InvComplex} (S : Commuting K)

theorem fgtR_castHR {a b : ℕ} (h : a = b) (z : HR (borelInv S) a) :
    fgtR S b (castHR h z) = castHR h (fgtR S a z) := by
  subst h
  rfl

/-- Forgetting the half rotation intertwines the reflection classes. -/
theorem fgtR_innerStep (q : ℕ) (x : HR (borelInv S) q) :
    fgtR S (q + 1) (innerStep S q x) = w K q (fgtR S q x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [innerStep_apply, fgtR_castHR, onHR_mk]
  have hs : seqOf S (1 + q) (((cyclesMap (innerW S) q c : bcocycles (borelInv S) (1 + q)) :
      Seq (borelInv S)) (1 + q)) = seqOf S q ((c : Seq (borelInv S)) q) := by
    change seqOf S (1 + q) (total (innerW S) (c : Seq (borelInv S)) (1 + q)) = _
    rw [total_at]
    rfl
  have hmem : seqOf S q ((c : Seq (borelInv S)) q) ∈ bcocycles K (q + 1) :=
    bcocycles_mono K q ((mem_cocycles_borelInv S q _).mp (forgetCocycle (borelInv S) q c).2)
  have hL : fgtR S (1 + q) (Submodule.Quotient.mk (cyclesMap (innerW S) q c)) =
      Submodule.Quotient.mk ⟨seqOf S (1 + q) (((cyclesMap (innerW S) q c :
        bcocycles (borelInv S) (1 + q)) : Seq (borelInv S)) (1 + q)),
        (mem_cocycles_borelInv S (1 + q) _).mp
          (forgetCocycle (borelInv S) (1 + q) (cyclesMap (innerW S) q c)).2⟩ := rfl
  rw [hL, castHR_mk _ _ _ (by rw [hs]; exact hmem)]
  change _ = (Submodule.Quotient.mk ⟨seqOf S q ((c : Seq (borelInv S)) q), hmem⟩ : HR K (q + 1))
  congr 1
  exact Subtype.ext hs

/-- Forgetting the half rotation kills its class. -/
theorem fgtR_v (q : ℕ) (x : HR (borelInv S) q) : fgtR S (q + 1) (w (borelInv S) q x) = 0 := by
  rw [fgtR_apply, (exact_forget (borelInv S) q _).mpr ⟨x, rfl⟩, map_zero]

theorem fgtR_innerPow (lo : ℕ) (x : HR (borelInv S) lo) : ∀ k : ℕ,
    fgtR S (lo + k) (NilpotentWK.innerPow S lo k x) = NilpotentW.wPow K lo k (fgtR S lo x)
  | 0 => rfl
  | k + 1 => by
    rw [NilpotentWK.innerPow_succ, NilpotentW.wPow_succ, ← fgtR_innerPow lo x k]
    exact fgtR_innerStep S (lo + k) _

theorem fgtR_wPow_succ (lo k : ℕ) (x : HR (borelInv S) lo) :
    fgtR S (lo + (k + 1)) (NilpotentW.wPow (borelInv S) lo (k + 1) x) = 0 := by
  rw [NilpotentW.wPow_succ]
  exact fgtR_v S _ _

/-- The classes annihilated by a power of U are stable under the reflection class. -/
theorem ann_innerStep (k : ℕ) : ∀ (q : ℕ) (x : HR (borelInv S) q), Ann S k q x →
    Ann S k (q + 1) (innerStep S q x) := by
  induction k with
  | zero =>
    intro q x hx
    change innerStep S q x = 0
    rw [show x = 0 from hx, map_zero]
  | succ k ih =>
    intro q x hx
    change Ann S k (q + 1 + 1 + 1) (opU S (q + 1) (innerStep S q x))
    have e : opU S (q + 1) (innerStep S q x) = innerStep S (q + 1 + 1) (opU S q x) := by
      rw [opU_apply, opU_apply, OperatorK.w_innerStep, ← map_add, OperatorK.w_innerStep]
    rw [e]
    exact ih _ _ hx

theorem ann_innerPow (k lo : ℕ) (x : HR (borelInv S) lo) (hx : Ann S k lo x) : ∀ j : ℕ,
    Ann S k (lo + j) (NilpotentWK.innerPow S lo j x)
  | 0 => hx
  | j + 1 => by
    rw [NilpotentWK.innerPow_succ]
    exact ann_innerStep S k _ _ (ann_innerPow k lo x hx j)

theorem ann_castHR {k a b : ℕ} (h : a = b) {x : HR (borelInv S) a} (hx : Ann S k a x) :
    Ann S k b (castHR h x) := by
  subst h
  exact hx

/-- v^k x = 0 implies U^k x = 0. -/
theorem ann_of_wPow : ∀ (k q : ℕ) (x : HR (borelInv S) q),
    NilpotentW.wPow (borelInv S) q k x = 0 → Ann S k q x := by
  intro k
  induction k with
  | zero => intro q x hx; exact hx
  | succ k ih =>
    intro q x hx
    change Ann S k (q + 1 + 1) (opU S q x)
    apply ih
    -- v^k (v (v x + w x)) = v^{k+1}(v x) + v^{k+1}(w x) = 0
    have hv : ∀ (j : ℕ) (y : HR (borelInv S) q), NilpotentW.wPow (borelInv S) q j y = 0 →
        ∀ i, NilpotentW.wPow (borelInv S) q (j + i) y = 0 := fun j y hy i =>
      wPow_zero_add hy i
    -- express v^k (opU x) through the powers of v on x
    have h1 : ∀ (j : ℕ) (y : HR (borelInv S) (q + 1)),
        NilpotentW.wPow (borelInv S) (q + 1 + 1) j (w (borelInv S) (q + 1) y) =
          castHR (by omega) (NilpotentW.wPow (borelInv S) (q + 1) (j + 1) y) := by
      intro j y
      induction j with
      | zero => rfl
      | succ j ihj =>
        rw [NilpotentW.wPow_succ, ihj, GlobalBasis.w_castHR]
        rfl
    have h2 : ∀ (j : ℕ), NilpotentW.wPow (borelInv S) (q + 1) j (w (borelInv S) q x) =
        castHR (by omega) (NilpotentW.wPow (borelInv S) q (j + 1) x) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        rw [NilpotentW.wPow_succ, ihj, GlobalBasis.w_castHR]
        rfl
    have h3 : ∀ (j : ℕ), NilpotentW.wPow (borelInv S) (q + 1) j (innerStep S q x) =
        castHR (by omega) (innerStep S (q + j) (NilpotentW.wPow (borelInv S) q j x)) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        rw [NilpotentW.wPow_succ, ihj, GlobalBasis.w_castHR, OperatorK.w_innerStep]
        rfl
    rw [opU_apply, h1, GlobalBasis.wPow_map_add, h2, h3, hx,
      show NilpotentW.wPow (borelInv S) q (k + 1 + 1) x = 0 from wPow_zero_add hx 1]
    simp only [map_zero, add_zero]

end Forget

/-! ### Connecting maps -/

section Delta

variable {K' K K'' : InvComplex} {S' : Commuting K'} {S : Commuting K} {S'' : Commuting K''}
  (I : CommHom S' S) (P : CommHom S S'') (h : ShortExact I.φ P.φ)

/-- The ordinary connecting map of the iterated sequence is the Borel connecting map. -/
theorem cohomologyEquiv_delta (q : ℕ) (z : H (borelInv S'') q) :
    cohomologyEquiv S' (q + 1)
        (OrdinaryDelta.delta (BorelQuasiIso.shortExact_iterated I P h) q z) =
      BorelExact.delta h q (cohomologyEquiv S'' q z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hK := BorelQuasiIso.shortExact_iterated I P h
  have hx : (borelInv S'').d q (x : (borelInv S'').C q) = 0 := x.2
  set y := BorelExact.sec (BorelQuasiIso.shortExact_iterated I P h) q (x : (borelInv S'').C q)
    with hy
  have hb : seqOf S q y ∈ low K (q + 1) := (toLow S q y).2
  have hπ : seqMap P.φ (seqOf S q y) =
      ((cocycleEquiv S'' q x : bcocycles K'' q) : Seq K'') := by
    have := BorelExact.proj_sec (BorelQuasiIso.shortExact_iterated I P h) q
      (x : (borelInv S'').C q)
    exact congrArg (seqOf S'' q) this
  set r := BorelExact.ret (BorelQuasiIso.shortExact_iterated I P h) (q + 1)
    ((borelInv S).d q y) with hr
  have hrι : (borelHom I).f (q + 1) r = (borelInv S).d q y :=
    OrdinaryDelta.incl_ret_d_sec (BorelQuasiIso.shortExact_iterated I P h) q _ hx
  have hrmem : seqOf S' (q + 1) r ∈ bcocycles K' (q + 1) :=
    (mem_cocycles_borelInv S' (q + 1) r).mp
      (OrdinaryDelta.deltaCocycle (BorelQuasiIso.shortExact_iterated I P h) q x).2
  have hz : seqMap I.φ (seqOf S' (q + 1) r) = D K (seqOf S q y) := by
    have := congrArg (seqOf S (q + 1)) hrι
    exact this
  have hR := delta_mk h q (cocycleEquiv S'' q x) (seqOf S q y) hb hπ ⟨_, hrmem⟩ hz
  have hc : cohomologyEquiv S'' q (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cocycleEquiv S'' q x) := rfl
  rw [hc, hR]
  rfl

/-- Forgetting the half rotation commutes with the connecting maps. -/
theorem fgtR_delta (q : ℕ) (y : HR (borelInv S'') q) :
    fgtR S' (q + 1) (BorelExact.delta (BorelQuasiIso.shortExact_iterated I P h) q y) =
      BorelExact.delta h q (fgtR S'' q y) := by
  rw [fgtR_apply, fgtR_apply, forget_delta, cohomologyEquiv_delta]

end Delta

/-! ### The lowest degree -/

section Low

variable {L : InvComplex}

/-- In the lowest degree, forgetting is surjective when the ordinary cohomology has dimension at
most one. -/
theorem forget_surjective_low {l : ℕ} (hbelow : ∀ q, q < l → ∀ y : HR L q, y = 0)
    [FiniteDimensional (ZMod 2) (H L l)] (hdim : finrank (ZMod 2) (H L l) ≤ 1) :
    Function.Surjective (forget L l) := by
  have hinj : Function.Injective (forget L l) := by
    cases l with
    | zero => exact BorelQuasiIso.forget_zero_injective L
    | succ l => exact forget_injective_of_w fun x => by rw [hbelow l (by omega) x, map_zero]
  by_cases h0 : ∀ z : H L l, z = 0
  · intro z
    exact ⟨0, by rw [map_zero, h0 z]⟩
  push_neg at h0
  obtain ⟨z, hz⟩ := h0
  have hz' : ∃ y, forget L l y = z := by
    by_cases ht : transfer L l z = 0
    · exact (exact_transfer L l z).mp ht
    · exfalso
      have hf : forget L l (transfer L l z) ≠ 0 := fun h0 => ht (hinj (by rw [h0, map_zero]))
      obtain ⟨c, hc⟩ := TowerSpan.exists_smul_of_finrank_le_one hdim hz
        (forget L l (transfer L l z))
      rcases zmod2_eq_zero_or_one c with hc0 | hc1
      · rw [hc0, zero_smul] at hc
        exact hf hc
      · rw [hc1, one_smul] at hc
        apply ht
        rw [← hc, (exact_transfer L l _).mpr ⟨_, rfl⟩]
  obtain ⟨y, hy⟩ := hz'
  intro z'
  obtain ⟨c, hc⟩ := TowerSpan.exists_smul_of_finrank_le_one hdim hz z'
  exact ⟨c • y, by rw [map_smul, hy, hc]⟩

/-- Forgetting the half rotation is bijective in the lowest degree of a pattern. -/
theorem fgtR_low {P : InvComplex} (SP : Commuting P) {l d : ℕ} (A : Pattern P l d) :
    Function.Surjective (fgtR SP l) ∧ Function.Injective (fgtR SP l) := by
  have hHbelow : ∀ q, q < l → ∀ z : H (borelInv SP) q, z = 0 := fun q hq z => by
    apply (cohomologyEquiv SP q).injective
    rw [A.HR_below q hq (cohomologyEquiv SP q z), map_zero]
  have hbelow := HR_zero_below hHbelow
  have hdimR : finrank (ZMod 2) (HR P l) ≤ 1 := by
    apply finrank_le_one A.τ
    intro x
    obtain ⟨c, hc⟩ := A.span_τ x
    exact ⟨c, hc.symm⟩
  have hfinR : FiniteDimensional (ZMod 2) (HR P l) := finite_HR A.fin l
  have : FiniteDimensional (ZMod 2) (H (borelInv SP) l) :=
    Module.Finite.equiv (cohomologyEquiv SP l).symm
  have hdim : finrank (ZMod 2) (H (borelInv SP) l) ≤ 1 := by
    rw [(cohomologyEquiv SP l).finrank_eq]
    exact hdimR
  have hsurj := forget_surjective_low hbelow hdim
  have hinj : Function.Injective (forget (borelInv SP) l) := by
    cases l with
    | zero => exact BorelQuasiIso.forget_zero_injective _
    | succ l => exact forget_injective_of_w fun x => by rw [hbelow l (by omega) x, map_zero]
  refine ⟨fun x => ?_, fun a b hab => hinj ((cohomologyEquiv SP l).injective hab)⟩
  obtain ⟨z, hz⟩ := hsurj ((cohomologyEquiv SP l).symm x)
  exact ⟨z, by rw [fgtR_apply, hz, LinearEquiv.apply_symm_apply]⟩

end Low

/-! ### K-filtrations -/

/-- A global filtration with commuting half rotations and the two local K-inputs. -/
structure KGlobal (d : ℕ) extends RGlobal d where
  l_zero : l 0 = d
  SG : Commuting G
  SZ : ∀ m, Commuting (Z m)
  SP : ∀ j, Commuting (P j)
  ST : ∀ m, Commuting (T m)
  ι_s : ∀ j k x, (ι j).f k ((SP j).s k x) = (SZ (j + 1)).s k ((ι j).f k x)
  π_s : ∀ j k x, (π j).f k ((SZ (j + 1)).s k x) = (SZ j).s k ((π j).f k x)
  ρ_s : ∀ m k x, (ρ m).f k (SG.s k x) = (SZ m).s k ((ρ m).f k x)
  κ_s : ∀ m k x, (κ m).f k ((ST m).s k x) = SG.s k ((κ m).f k x)
  vnil : ∀ j, Even j → ∀ lo (x : HR (borelInv (SP j)) lo),
    NilpotentW.wPow (borelInv (SP j)) lo (d + 2) x = 0
  ytop : ∀ j, Odd j → ∃ y : HR (borelInv (SP j)) (d + 1 + l j),
    fgtR (SP j) (d + 1 + l j) y = EP j (l j) (pattern j).τ

variable {d : ℕ} (K : KGlobal d)

namespace KGlobal

def cι (j : ℕ) : CommHom (K.SP j) (K.SZ (j + 1)) := ⟨K.ι j, K.ι_s j⟩
def cπ (j : ℕ) : CommHom (K.SZ (j + 1)) (K.SZ j) := ⟨K.π j, K.π_s j⟩
def cρ (m : ℕ) : CommHom K.SG (K.SZ m) := ⟨K.ρ m, K.ρ_s m⟩
def cκ (m : ℕ) : CommHom (K.ST m) K.SG := ⟨K.κ m, K.κ_s m⟩

theorem l_eq (j : ℕ) : K.l j = (2 * j + 1) * d := by
  induction j with
  | zero => rw [K.l_zero]; ring
  | succ j ih => rw [K.l_succ, ih]; ring

/-- The iterated tail sequences. -/
theorem kexactT (m : ℕ) : ShortExact (borelHom (K.cκ m)) (borelHom (K.cρ m)) :=
  BorelQuasiIso.shortExact_iterated (K.cκ m) (K.cρ m) (K.exactT m)

theorem HR_kT_zero (m q : ℕ) (hq : q < K.l m) (x : HR (borelInv (K.ST m)) q) : x = 0 := by
  have hH : ∀ q', q' < K.l m → ∀ z : H (borelInv (K.ST m)) q', z = 0 := fun q' hq' z => by
    apply (cohomologyEquiv (K.ST m) q').injective
    rw [K.toRGlobal.HR_T_zero m q' hq' (cohomologyEquiv (K.ST m) q' z), map_zero]
  exact HR_zero_below hH q hq x

theorem ρK_injective_low (m q : ℕ) (hq : q < K.l m) :
    Function.Injective (HRmap (borelHom (K.cρ m)) q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := exact_mid (K.kexactT m) q x hx
  rw [K.HR_kT_zero m q hq z, map_zero]

/-- The tail inclusion is injective on reflection Borel cohomology. -/
theorem κ_injective (m q : ℕ) : Function.Injective (HRmap (K.κ m) q) := by
  cases q with
  | zero => exact injective_zero (K.exactT m)
  | succ q =>
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := exact_sub (K.exactT m) q y hy
    obtain ⟨x', rfl⟩ := K.toRGlobal.ρ_surjective m q x
    exact delta_comp_zero (K.exactT m) q x'

theorem fgtR_T_injective (m : ℕ) : Function.Injective (fgtR (K.ST m) (K.l m)) := by
  intro a b hab
  have hinj : Function.Injective (forget (borelInv (K.ST m)) (K.l m)) := by
    cases hl : K.l m with
    | zero => exact BorelQuasiIso.forget_zero_injective _
    | succ l =>
      exact forget_injective_of_w fun x => by
        rw [K.HR_kT_zero m l (by omega) x, map_zero]
  exact hinj ((cohomologyEquiv (K.ST m) _).injective hab)

/-- A global K-class vanishing at the stage m and after forgetting the half rotation vanishes,
in degrees up to the lowest degree of the next crossing. -/
theorem eq_zero_of_ρK (m q : ℕ) (hq : q ≤ K.l m) (y : HR (borelInv K.SG) q)
    (hρ : HRmap (borelHom (K.cρ m)) q y = 0) (hf : fgtR K.SG q y = 0) : y = 0 := by
  rcases Nat.lt_or_ge q (K.l m) with hlt | hge
  · exact K.ρK_injective_low m q hlt (by rw [hρ, map_zero])
  · have hqe : q = K.l m := le_antisymm hq hge
    subst hqe
    obtain ⟨t, rfl⟩ := exact_mid (K.kexactT m) _ y hρ
    have ht : fgtR (K.ST m) (K.l m) t = 0 := by
      apply K.κ_injective m
      rw [map_zero]
      exact (fgtR_natural (K.cκ m) _ t).symm.trans hf
    rw [K.fgtR_T_injective m (by rw [ht, map_zero] : fgtR (K.ST m) (K.l m) t =
      fgtR (K.ST m) (K.l m) 0), map_zero]

/-- A K-class of the stage m whose forgetful image is the restriction of a global class extends
to a global K-class, in degrees below the lowest degree of the next crossing. -/
theorem ρK_lift (m q : ℕ) (hq : q + 1 ≤ K.l m) (y : HR (borelInv (K.SZ m)) q)
    (hy : ∃ x : HR K.G q, HRmap (K.ρ m) q x = fgtR (K.SZ m) q y) :
    ∃ Y, HRmap (borelHom (K.cρ m)) q Y = y := by
  obtain ⟨x, hx⟩ := hy
  apply exact_delta (K.kexactT m) q y
  have hf : fgtR (K.ST m) (q + 1) (BorelExact.delta (K.kexactT m) q y) = 0 := by
    rw [fgtR_delta (K.cκ m) (K.cρ m) (K.exactT m), ← hx]
    exact delta_comp_zero (K.exactT m) q x
  rcases Nat.lt_or_ge (q + 1) (K.l m) with hlt | hge
  · exact K.HR_kT_zero m (q + 1) hlt _
  · have hqe : q + 1 = K.l m := le_antisymm hq hge
    have hinj := K.fgtR_T_injective m
    rw [← hqe] at hinj
    exact hinj (by rw [hf, map_zero])

/-! ### The global K-lifts -/

/-- The K-lift of the bottom class of the crossing j. -/
def τK (j : ℕ) : HR (borelInv (K.SP j)) (K.l j) :=
  Classical.choose ((fgtR_low (K.SP j) (K.pattern j)).1 (K.pattern j).τ)

theorem fgtR_τK (j : ℕ) : fgtR (K.SP j) (K.l j) (K.τK j) = (K.pattern j).τ :=
  Classical.choose_spec ((fgtR_low (K.SP j) (K.pattern j)).1 (K.pattern j).τ)

theorem l_add_lt (j : ℕ) : K.l j + d + 2 ≤ K.l (j + 1) := by
  have := K.l_succ j
  have := K.two_le
  omega

theorem exists_ζ (j : ℕ) : ∃ Y, HRmap (borelHom (K.cρ (j + 1))) (K.l j) Y =
    HRmap (borelHom (K.cι j)) (K.l j) (K.τK j) := by
  apply K.ρK_lift (j + 1) (K.l j) (by have := K.l_add_lt j; omega)
  refine ⟨K.toRGlobal.X j, ?_⟩
  rw [fgtR_natural (K.cι j), K.fgtR_τK]
  exact K.toRGlobal.ρ_X j

/-- The global K-lift of the bottom class X_j. -/
def ζ (j : ℕ) : HR (borelInv K.SG) (K.l j) := Classical.choose (K.exists_ζ j)

theorem ρK_ζ (j : ℕ) : HRmap (borelHom (K.cρ (j + 1))) (K.l j) (K.ζ j) =
    HRmap (borelHom (K.cι j)) (K.l j) (K.τK j) := Classical.choose_spec (K.exists_ζ j)

theorem fgtR_ζ (j : ℕ) : fgtR K.SG (K.l j) (K.ζ j) = K.toRGlobal.X j := by
  apply K.toRGlobal.ρ_injective_low (j + 1) (K.l j) (by have := K.l_add_lt j; omega)
  have h1 := fgtR_natural (K.cρ (j + 1)) (K.l j) (K.ζ j)
  rw [K.ρK_ζ, fgtR_natural (K.cι j), K.fgtR_τK] at h1
  exact h1.symm.trans (K.toRGlobal.ρ_X j).symm

/-- For even j the K-lift is annihilated by a power of v. -/
theorem v_ζ (j : ℕ) (he : Even j) :
    NilpotentW.wPow (borelInv K.SG) (K.l j) (d + 2) (K.ζ j) = 0 := by
  apply K.eq_zero_of_ρK (j + 1) (K.l j + (d + 2)) (by have := K.l_add_lt j; omega)
  · rw [NilpotentW.HRmap_wPow, K.ρK_ζ, ← NilpotentW.HRmap_wPow, K.vnil j he, map_zero]
  · exact fgtR_wPow_succ K.SG (K.l j) (d + 1) (K.ζ j)

/-- For even j the K-lift is annihilated by U^{d+2}. -/
theorem ann_ζ (j : ℕ) (he : Even j) : Ann K.SG (d + 2) (K.l j) (K.ζ j) :=
  ann_of_wPow K.SG (d + 2) (K.l j) (K.ζ j) (K.v_ζ j he)

theorem exists_Y (j : ℕ) (ho : Odd j) : ∃ Y : HR (borelInv K.SG) (d + 1 + K.l j),
    fgtR K.SG (d + 1 + K.l j) Y = K.E (K.l j) (K.toRGlobal.X j) := by
  obtain ⟨y, hy⟩ := K.ytop j ho
  obtain ⟨Y, hY⟩ := K.ρK_lift (j + 1) (d + 1 + K.l j) (by have := K.l_add_lt j; omega)
    (HRmap (borelHom (K.cι j)) (d + 1 + K.l j) y) ⟨K.E (K.l j) (K.toRGlobal.X j), by
      rw [K.E_ρ, fgtR_natural (K.cι j), hy]
      change _ = HRmap (K.ι j) _ _
      rw [K.E_ι, K.toRGlobal.ρ_X j]⟩
  refine ⟨Y, ?_⟩
  apply K.toRGlobal.ρ_injective_low (j + 1) _ (by have := K.l_add_lt j; omega)
  have h1 := fgtR_natural (K.cρ (j + 1)) (d + 1 + K.l j) Y
  rw [hY, fgtR_natural (K.cι j), hy] at h1
  change HRmap (K.ι j) _ _ = HRmap (K.ρ (j + 1)) _ _ at h1
  rw [K.E_ι, ← K.toRGlobal.ρ_X j, ← K.E_ρ] at h1
  exact h1.symm

/-! ### The basis data -/

/-- The evaluation operator commutes with degree casts. -/
theorem E_castHR {a b : ℕ} (h : a = b) (x : HR K.G a) :
    K.E b (castHR h x) = castHR (congrArg (d + 1 + ·) h) (K.E a x) := by
  subst h
  rfl

/-- Every bottom class lifts; on bottom degrees of even stages the lift is U-torsion. -/
theorem lift_bot (q : ℕ) : ∃ z : HR (borelInv K.SG) q,
    ((∀ j, K.toRGlobal.IsBot j q → Even j → Ann K.SG (d + 2) q z)) ∧
      fgtR K.SG q z = K.toRGlobal.bot q := by
  by_cases h : ∃ j, K.toRGlobal.IsBot j q
  · obtain ⟨j, hj⟩ := h
    refine ⟨castHR (Nat.add_sub_cancel' hj.1)
      (NilpotentWK.innerPow K.SG (K.l j) (q - K.l j) (K.ζ j)), ?_, ?_⟩
    · intro j' hj' he
      have hjj := K.toRGlobal.isBot_unique hj hj'
      subst hjj
      exact ann_castHR K.SG _ (ann_innerPow K.SG _ _ _ (K.ann_ζ j he) _)
    · rw [K.toRGlobal.bot_of hj, fgtR_castHR, fgtR_innerPow, K.fgtR_ζ]
      rfl
  · refine ⟨0, fun j hj _ => absurd ⟨j, hj⟩ h, ?_⟩
    rw [map_zero, K.toRGlobal.bot_zero h]

/-- Every top class of an odd stage, or of no stage, lifts. -/
theorem lift_top (q : ℕ)
    (hq : ∀ q', (∃ j, Even j ∧ K.toRGlobal.IsBot j q') → q ≠ d + 1 + q') :
    ∃ z : HR (borelInv K.SG) q, fgtR K.SG q z = K.toRGlobal.top q := by
  by_cases hd1 : d + 1 ≤ q
  · by_cases h : ∃ j, K.toRGlobal.IsBot j (q - (d + 1))
    · obtain ⟨j, hj⟩ := h
      rcases Nat.even_or_odd j with he | ho
      · exact absurd (by omega) (hq (q - (d + 1)) ⟨j, he, hj⟩)
      · obtain ⟨Y, hY⟩ := K.exists_Y j ho
        have hk : d + 1 + K.l j + (q - (d + 1) - K.l j) = q := by
          have := hj.1
          omega
        refine ⟨castHR hk (NilpotentWK.innerPow K.SG (d + 1 + K.l j) (q - (d + 1) - K.l j) Y),
          ?_⟩
        rw [fgtR_castHR, fgtR_innerPow, hY]
        rw [GlobalBasis.RGlobal.top, dif_pos hd1, K.toRGlobal.bot_of hj, E_castHR,
          castHR_castHR]
        have e1 := K.toRGlobal.Tw_eq j (q - (d + 1) - K.l j)
        rw [GlobalBasis.RGlobal.Tw] at e1
        rw [e1, castHR_castHR]
    · refine ⟨0, ?_⟩
      rw [map_zero, GlobalBasis.RGlobal.top, dif_pos hd1, K.toRGlobal.bot_zero h, map_zero,
        map_zero]
  · refine ⟨0, ?_⟩
    rw [map_zero, GlobalBasis.RGlobal.top, dif_neg hd1]

end KGlobal

/-- The global basis data, in the form of `BasisBudget.Data`, for an abstract pair. -/
structure AbsData (G : InvComplex) (SG : Commuting G) (n : ℕ)
    (E : ∀ q, HR G q →ₗ[ZMod 2] HR G (n + q)) where
  bot : ∀ q, HR G q
  top : ∀ q, HR G q
  odd : ℕ → Prop
  torsion : ℕ
  span : ∀ q (x : HR G q), ∃ c c' : ZMod 2, x = c • bot q + c' • top q
  top_eq : ∀ q, odd q → top (n + q) = E q (bot q)
  lift_bot : ∀ q, ∃ z : HR (borelInv SG) q, fgtR SG q z = bot q
  lift_odd : ∀ q, odd q → ∃ z : HR (borelInv SG) q, Ann SG torsion q z ∧ fgtR SG q z = bot q
  lift_top : ∀ q, (∀ q', odd q' → q ≠ n + q') → ∃ z : HR (borelInv SG) q, fgtR SG q z = top q
  odd_mem : ∀ t : ℕ, odd ((4 * t + 1) * (n - 1))
  bot_ne : ∀ t : ℕ, bot ((4 * t + 1) * (n - 1)) ≠ 0

namespace KGlobal

/-- A K-filtration gives the global basis data. -/
def absData : AbsData K.G K.SG (d + 1) K.E where
  bot := K.toRGlobal.bot
  top := K.toRGlobal.top
  odd q := ∃ j, Even j ∧ K.toRGlobal.IsBot j q
  torsion := d + 2
  span := K.toRGlobal.span
  top_eq q _ := K.toRGlobal.top_eq q
  lift_bot q := by
    obtain ⟨z, _, hz⟩ := K.lift_bot q
    exact ⟨z, hz⟩
  lift_odd q hq := by
    obtain ⟨j, he, hj⟩ := hq
    obtain ⟨z, hann, hz⟩ := K.lift_bot q
    exact ⟨z, hann j hj he, hz⟩
  lift_top q hq := K.lift_top q hq
  odd_mem t := by
    have e : (4 * t + 1) * (d + 1 - 1) = K.l (2 * t) := by
      rw [K.l_eq, show d + 1 - 1 = d by omega]
      ring
    refine ⟨2 * t, ⟨t, by ring⟩, ?_, ?_⟩
    · rw [e]
    · rw [e]
      omega
  bot_ne t := by
    have e : (4 * t + 1) * (d + 1 - 1) = K.l (2 * t) := by
      rw [K.l_eq, show d + 1 - 1 = d by omega]
      ring
    rw [e]
    exact K.toRGlobal.bot_ne (2 * t)

/-- The power w^{d+1} vanishes on the global reflection Borel cohomology. -/
theorem w_nil (lo : ℕ) (x : HR K.G lo) : NilpotentW.wPow K.G lo (d + 1) x = 0 :=
  K.toRGlobal.w_nil lo x

end KGlobal

end

end Finsler.GlobalK
