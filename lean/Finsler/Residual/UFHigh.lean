module

public import Finsler.Residual.UFCore
public import Finsler.Residual.BLF

/-! Uniform filling in high degrees from cut data (Claude, UF prototype, assembly).

For every r let T_r cut lengths by L_r (a representative of the r-th GH power vanishing on t_{L_r},
ℓ_r − 1 ≤ L_r < ℓ_r) and let S_r be a filtered class at length s_r whose cut is the filtered unit at
length B_r, with s_r − L_r ≤ Δ and B_r ≤ B* (`CutData`). For a globally null class x at length a in a
high degree q choose r = min (r_len a) (r_deg q): the largest r with ℓ_r ≤ a, and the r putting the
cut in the window of degrees [i₀, i₀ + 2m). The cut of x then either lies at a bounded length (BLF)
or in a window degree (WF, BLF), and `UFCore.kill` kills x within a uniform extra length. -/

@[expose] public section

namespace Finsler.UFHigh

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
open Finsler.SupportedCapNaturality Finsler.BorelCochain

noncomputable section
set_option autoImplicit false

variable (m : ℕ) (F : ReversibleMetric (m + 1)) (ε : ℝ) (hε : 0 < ε)

/-- The cut data of the r-th powers. -/
structure CutData (r : ℕ) where
  L : ℝ
  s : ℝ
  T : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m r)
  hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m r) T = 0
  hsh : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L))
    (NativeGHPowers.degree m r) T = 0
  S : PoolCap.homology (lengthSpace F s) ((m + NativeGHPowers.degree m r) + (m + 1))
  hs0 : 0 < s
  hsa : 0 < s - L + 3 * ε
  B : ℝ
  hB : 0 < B
  hBs : s - L + 3 * ε ≤ B
  hunit : UFCore.enl F hBs (m + 1)
      (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε T hT hsh
        (a := s)).homology (m + 1)).hom S) =
    StrictLengthFilteredUnit.candidate F (by omega) B hB

/-- The least r whose next GH level exceeds a. -/
theorem exists_level_gt (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {C : ℝ}
    (hC : ∀ r : ℕ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C ≤ NativeGHSpectralSupport.level m F r)
    (a : ℝ) : ∃ r : ℕ, a < NativeGHSpectralSupport.level m F (r + 1) := by
  have hβ := NativeGHOptimalRate.rate_positive m hm F P v₀
  obtain ⟨r, hr⟩ := exists_nat_gt ((a + C) / NativeGHOptimalRate.rate m F)
  refine ⟨r, ?_⟩
  have h1 := hC (r + 1)
  have h2 : a + C < (r : ℝ) * NativeGHOptimalRate.rate m F := by
    rw [div_lt_iff₀ hβ] at hr
    linarith
  push_cast at h1
  nlinarith

theorem level_succ_ge (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    NativeGHSpectralSupport.level m F r ≤ NativeGHSpectralSupport.level m F (r + 1) := by
  have h := NativeGHSpectralSupport.level_add m hm F P v₀ r 0
  have h0 := NativeThetaGHRateDeficit.gh_level_positive m hm F P v₀ 0
  simp only [add_zero] at h
  linarith

theorem level_mono (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {r r' : ℕ} (h : r ≤ r') :
    NativeGHSpectralSupport.level m F r ≤ NativeGHSpectralSupport.level m F r' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (level_succ_ge m F hm P v₀ _)

/-- The cut of a globally null class is globally null. -/
theorem cut_null (hm : 1 ≤ m) {a L : ℝ} (p : ℕ) (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hsh : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F L)) p T = 0)
    (i : ℕ) (x : homologyZMod2 (lengthSpace F a) ((m + p) + i))
    (hx : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) ((m + p) + i)).hom x = 0) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (a - L + 3 * ε)) i).hom
      (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hsh (a := a)).homology i).hom x) = 0 := by
  have h := CanonicalGlobalSelfCutFiltered.original_filtered m hm p F hε T hT hsh i x
  refine h.trans ?_
  change (CanonicalGlobalSelfCut.map m p i (cocycleClass _ p T hT)).hom
    ((homologyPushZMod2 (LengthFilteredLoopRotation.full F a) ((m + p) + i)).hom x) = 0
  rw [hx, map_zero]

/-- A class at a regular length c dying in the loop space dies after the uniform BLF length, or,
in a window degree above c_max, is already zero at the next regular length. -/
theorem cut_fill (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) {L₃ B₀ : ℝ}
    (hL₃ : 0 < L₃) (hB₀ : L₃ ≤ B₀)
    (hblf : ∀ i : ℕ, (m + 1) + 1 < i → ∀ y : homologyZMod2 (lengthSpace F L₃) i,
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F L₃) i).hom y = 0 →
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hB₀) i).hom y = 0)
    {c : ℝ} (hc : 0 < c) (hcL : c ≤ L₃) (i : ℕ) (hi : (m + 1) + 1 < i)
    (y : homologyZMod2 (lengthSpace F c) i)
    (hy : (homologyPushZMod2 (LengthFilteredLoopRotation.full F c) i).hom y = 0) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.cut F (hcL.trans hB₀)) i).hom y = 0 := by
  have hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F L₃) i).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F hcL) i).hom y) = 0 := by
    rw [push_comp_apply]
    exact hy
  have h := hblf i hi _ hz
  rw [push_comp_apply] at h
  exact h

open Finsler.CriticalLevels Finsler.BorelCrossing in
/-- **Killing one class** with the cut data of r. -/
theorem kill_at (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) (r : ℕ)
    (d : CutData m F ε hε r) {a : ℝ} (ha : 0 < a) (hLa : d.L < a)
    (i₀ i : ℕ) (hi : (m + 1) + 1 < i)
    {L₃ B₀ : ℝ} (hL₃ : 0 < L₃) (hB₀ : L₃ ≤ B₀)
    (hblf : ∀ j : ℕ, (m + 1) + 1 < j → ∀ y : homologyZMod2 (lengthSpace F L₃) j,
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F L₃) j).hom y = 0 →
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hB₀) j).hom y = 0)
    {cmax : ℝ} (hcmax : cmax ≤ L₃)
    (hwin : i < i₀ + 2 * m → ∀ (b : ℝ), cmax ≤ b → ∀ (a' b' : ℝ) (hab' : a' ≤ b'), cmax ≤ a' → b' ≤ b →
      a' ∉ crit F → b' ∉ crit F → (crit F ∩ Set.Icc a' b').Subsingleton →
      (∀ z : H (crossComplex F hab') i, z = 0) ∧ ∀ z : H (crossComplex F hab') (i + 1), z = 0)
    (hcase : a - d.L + 3 * ε ≤ L₃ ∨ i < i₀ + 2 * m)
    {Δ Bs : ℝ} (hΔ : d.s - d.L ≤ Δ) (hBB : d.B ≤ Bs)
    (x : PoolCap.homology (lengthSpace F a) ((m + NativeGHPowers.degree m r) + i))
    (hx : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) _).hom x = 0)
    (D : ℝ) (hD1 : Bs + ε ≤ D) (hD2 : Δ + 6 * ε ≤ D) (hD3 : Δ + 4 * ε + max B₀ 1 ≤ D) :
    UFCore.enl F (by linarith [le_max_right B₀ 1, d.hsa] : a ≤ a + D) _ x = 0 := by
  set c := a - d.L + 3 * ε with hcdef
  have hc : 0 < c := by linarith
  have hnull := cut_null m F ε hε (by omega) _ d.T d.hT d.hsh i x hx
  -- the filling of the cut of x
  obtain ⟨D₀, hD₀0, hD₀le, hfill⟩ : ∃ D₀ : ℝ, ∃ h0 : 0 ≤ D₀, D₀ ≤ max B₀ 1 ∧
      UFCore.enl F (by linarith [h0] : c ≤ c + D₀) i
        (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε d.T d.hT d.hsh
          (a := a)).homology i).hom x) = 0 := by
    by_cases hcL : c ≤ L₃
    · refine ⟨B₀ - c, by linarith, by linarith [le_max_left B₀ 1], ?_⟩
      have h := cut_fill m F hm hfin hL₃ hB₀ hblf hc hcL i hi _ hnull
      exact UFBLF.enl_zero_mono m F (hcL.trans hB₀) (by linarith : B₀ ≤ c + (B₀ - c)) i _ h
    · have hwi : i < i₀ + 2 * m := hcase.resolve_left hcL
      obtain ⟨c', hc'1, hc'2, hc'c⟩ := Finsler.ComparisonBasic.exists_regular_between (F := F) hfin c
      refine ⟨c' - c, by linarith, by linarith [le_max_right B₀ 1], ?_⟩
      have hcc' : c ≤ c' := hc'1.le
      have hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F c') i).hom
          ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F hcc') i).hom
            (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε d.T d.hT d.hsh
              (a := a)).homology i).hom x)) = 0 := by
        exact (push_comp_apply (LengthFilteredLoopRotation.cut F hcc')
          (LengthFilteredLoopRotation.full F c') i _).trans hnull
      have hk := UFWindow.window_kill m F hfin (hc.trans hc'1) hc'c i hi
        (fun b hb a' b' hab' ha' hb' h1 h2 h3 =>
          hwin hwi b (by linarith) a' b' hab' (by linarith) hb' h1 h2 h3) _ hz
      exact UFBLF.enl_zero_mono m F hcc' (by linarith : c' ≤ c + (c' - c)) i _ hk
  exact UFCore.kill F (by omega) hε d.hs0 ha hc d.hsa d.hB d.hBs hD₀0 _ d.T d.hT d.hsh i (by omega) x
    d.S d.hunit hfill (a + D) (by linarith) (by linarith) (by linarith)

open Finsler.CriticalLevels Finsler.BorelCrossing in
/-- **Uniform filling in high degrees from cut data.** -/
theorem uf_of_data (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite)
    (P : Sphere (m + 1)) (v₀ : equator P)
    (data : ∀ r : ℕ, CutData m F ε hε r)
    {Δ Bs C : ℝ} (hΔ : ∀ r, (data r).s - (data r).L ≤ Δ) (hBs : ∀ r, (data r).B ≤ Bs)
    (hL : ∀ r, (data r).L < NativeGHSpectralSupport.level m F r ∧
      NativeGHSpectralSupport.level m F r - 1 ≤ (data r).L)
    (hC : ∀ r : ℕ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C ≤ NativeGHSpectralSupport.level m F r ∧
      NativeGHSpectralSupport.level m F r ≤ ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + C)
    (i₀ : ℕ) (hi₀ : (m + 1) + 1 < i₀) {cmax : ℝ}
    (hwin : ∀ i : ℕ, i₀ ≤ i → i < i₀ + 2 * m → ∀ (b : ℝ), cmax ≤ b → ∀ (a' b' : ℝ) (hab' : a' ≤ b'),
      cmax ≤ a' → b' ≤ b → a' ∉ crit F → b' ∉ crit F → (crit F ∩ Set.Icc a' b').Subsingleton →
      (∀ z : H (crossComplex F hab') i, z = 0) ∧ ∀ z : H (crossComplex F hab') (i + 1), z = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : ℝ) (ha : 0 < a) (q : ℕ), i₀ + 2 * m ≤ q →
      ∀ x : PoolCap.homology (lengthSpace F a) q,
        (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) q).hom x = 0 →
        ∀ h : a ≤ a + D, UFCore.enl F h q x = 0 := by
  set β := NativeGHOptimalRate.rate m F with hβdef
  have hβ := NativeGHOptimalRate.rate_positive m hm F P v₀
  have hC0 : 0 ≤ C := by linarith [(hC 0).1, (hC 0).2]
  -- the BLF length
  obtain ⟨L₃, hL₃1, -, hL₃c⟩ := Finsler.ComparisonBasic.exists_regular_between (F := F) hfin
    (max cmax (2 * β + 2 * C + 2 + 3 * ε))
  have hL₃0 : 0 < L₃ := lt_of_le_of_lt (le_trans (by positivity) (le_max_right _ _)) hL₃1
  obtain ⟨B₀, hB₀, hblf⟩ := UFBLF.blf_high m F hfin hL₃0 hL₃c
  have hΔ0 : -3 * ε < Δ := by linarith [hΔ 0, (data 0).hsa]
  refine ⟨max (Bs + ε) (max (Δ + 6 * ε) (Δ + 4 * ε + max B₀ 1)), ?_, ?_⟩
  · have := le_max_right (Bs + ε) (max (Δ + 6 * ε) (Δ + 4 * ε + max B₀ 1))
    have := le_max_right (Δ + 6 * ε) (Δ + 4 * ε + max B₀ 1)
    have := le_max_right B₀ 1
    linarith
  intro a ha q hq x hx hD
  set D := max (Bs + ε) (max (Δ + 6 * ε) (Δ + 4 * ε + max B₀ 1)) with hDdef
  have hD1 : Bs + ε ≤ D := le_max_left _ _
  have hD2 : Δ + 6 * ε ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD3 : Δ + 4 * ε + max B₀ 1 ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hB₀D : B₀ ≤ a + D := by linarith [le_max_left B₀ 1]
  have hcL3 : cmax ≤ L₃ := (le_max_left _ _).trans hL₃1.le
  have hbL3 : 2 * β + 2 * C + 2 + 3 * ε ≤ L₃ := (le_max_right _ _).trans hL₃1.le
  by_cases hal : a < NativeGHSpectralSupport.level m F 0
  · -- bounded length: direct BLF
    have haL : a ≤ L₃ := by
      have := (hC 0).2
      push_cast at this
      linarith
    have h := cut_fill m F hm hfin hL₃0 hB₀ hblf ha haL q (by omega) x hx
    exact UFBLF.enl_zero_mono m F (haL.trans hB₀) hB₀D q x h
  · rw [not_lt] at hal
    classical
    have hex := exists_level_gt m F hm P v₀ (fun r => (hC r).1) a
    set r₀ := Nat.find hex with hr₀def
    have hr₀ : a < NativeGHSpectralSupport.level m F (r₀ + 1) := Nat.find_spec hex
    have hr₀' : NativeGHSpectralSupport.level m F r₀ ≤ a := by
      rcases Nat.eq_zero_or_pos r₀ with h0 | hpos
      · rw [h0]; exact hal
      · obtain ⟨k, hk⟩ : ∃ k, r₀ = k + 1 := ⟨r₀ - 1, by omega⟩
        have hmin := Nat.find_min hex (show k < r₀ by omega)
        rw [hk]
        exact not_lt.mp hmin
    have hexd : ∃ r : ℕ, q < (2 * r + 4) * m + i₀ := ⟨q, by nlinarith⟩
    set rd := Nat.find hexd with hrddef
    have hrd1 : q < (2 * rd + 4) * m + i₀ := Nat.find_spec hexd
    have hrd2 : (2 * rd + 2) * m + i₀ ≤ q := by
      rcases Nat.eq_zero_or_pos rd with h0 | hpos
      · rw [h0]; omega
      · obtain ⟨k, hk⟩ : ∃ k, rd = k + 1 := ⟨rd - 1, by omega⟩
        have hmin := Nat.find_min hexd (show k < rd by omega)
        rw [not_lt] at hmin
        rw [hk]
        have : (2 * (k + 1) + 2) * m = (2 * k + 4) * m := by ring
        omega
    set r := min r₀ rd with hrdef
    have hℓr : NativeGHSpectralSupport.level m F r ≤ a :=
      (level_mono m F hm P v₀ (min_le_left _ _)).trans hr₀'
    have hrle : (2 * r + 2) * m ≤ (2 * rd + 2) * m :=
      Nat.mul_le_mul_right _ (by have := min_le_right r₀ rd; omega)
    have hdeg : m + NativeGHPowers.degree m r = (2 * r + 2) * m := by
      rw [NativeGHPowers.degree_formula]; ring
    obtain ⟨X, hX⟩ : ∃ X, X = (2 * r + 2) * m := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, Y = (2 * rd + 2) * m := ⟨_, rfl⟩
    have hY4 : (2 * rd + 4) * m = Y + 2 * m := by rw [hY]; ring
    rw [← hX] at hrle hdeg
    rw [← hY] at hrle hrd2
    rw [hY4] at hrd1
    obtain ⟨i, hqi⟩ : ∃ i, q = (m + NativeGHPowers.degree m r) + i :=
      ⟨q - (m + NativeGHPowers.degree m r), by omega⟩
    have hi0 : i₀ ≤ i := by omega
    have hcase : a - (data r).L + 3 * ε ≤ L₃ ∨ i < i₀ + 2 * m := by
      by_cases hrr : r₀ ≤ rd
      · left
        have hr : r = r₀ := min_eq_left hrr
        have hℓ : NativeGHSpectralSupport.level m F r = NativeGHSpectralSupport.level m F r₀ := by
          rw [hr]
        have h1 := (hL r).2
        have h2 := (hC (r₀ + 1)).2
        have h3 := (hC r₀).1
        have hβ' : 0 < β := hβ
        push_cast at h2
        linarith
      · right
        have hr : r = rd := min_eq_right (by omega)
        have : X = Y := by rw [hX, hY, hr]
        omega
    have hLa : (data r).L < a := (hL r).1.trans_le hℓr
    have hi2 : (m + 1) + 1 < i := by omega
    revert x hx
    rw [hqi]
    intro x hx
    exact kill_at m F ε hε hm hfin r (data r) ha hLa i₀ i hi2 hL₃0 hB₀ hblf hcL3
      (fun hw => hwin i hi0 hw) hcase (hΔ r) (hBs r) x hx D hD1 hD2 hD3

end

end Finsler.UFHigh
