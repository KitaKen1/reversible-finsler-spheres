module

public import Finsler.Residual.UFHigh
public import Finsler.Residual.FullHRAbs
public import Finsler.Residual.HRBridge

/-! The cut data of all GH powers with one unit length (Claude, UF prototype).

For every r: T_r represents the r-th GH power and vanishes on t_{ℓ_r − 1/2}; S_r is a filtered lift of
the r-th Theta power at length t_r + 1/2. The cut of S_r is globally the constant unit (the
high-power UNIT), lives below the fixed length c* = β + C + 1 + 3ε (exact rates), and therefore
agrees with the filtered unit at one length B* for all r (bounded-length filling in degree n). -/

@[expose] public section

namespace Finsler.UFData

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
open Finsler.SupportedCapNaturality

noncomputable section
set_option autoImplicit false

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P)

/-- The cutting length of the r-th power. -/
abbrev cutL (r : ℕ) : ℝ := NativeGHSpectralSupport.level m F r - 1 / 2

include hm in
theorem power_vanish (r : ℕ) :
    (cohPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F (cutL m F r)))
      (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 :=
  NativeGHSpectralSupport.restriction_below m hm F r (by simp only [cutL]; linarith)

/-- The representative of the r-th power vanishing on t_{L_r}. -/
abbrev rep (r : ℕ) := NormalizedRelativeRepresentative.raw (Loops (m + 1))
  (SelfCutOscillation.short F (cutL m F r)) (NativeGHPowers.degree m r) (NativeGHPowers.power m r)
  (power_vanish m hm F r)

/-- The global cut of a filtered lift of the r-th Theta power is the global unit. -/
theorem cut_unit_global (r : ℕ) {ε : ℝ} (hε : 0 < ε) {s : ℝ}
    (z₀ : homologyZMod2 (lengthSpace F s) (NativeThetaPowers.degree m r))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F s) _).hom z₀ =
      NativeThetaPowers.fullPower m hm F P v₀ r) (b : ℝ) (hb : 0 < b) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (s - cutL m F r + 3 * ε)) (m + 1)).hom
        (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε (rep m hm F r)
          (NormalizedRelativeRepresentative.raw_closed _ _ _ _ _)
          (NormalizedRelativeRepresentative.raw_supported _ _ _ _ _) (a := s)).homology (m + 1)).hom
          (ThetaRaise.aligned m F r z₀)) =
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) (m + 1)).hom
        (StrictLengthFilteredUnit.candidate F (by omega) b hb) := by
  have hi : Function.Injective (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom := by
    intro x y h
    have h' := congrArg (homologyPushZMod2 (FullLoopModel.forget (m + 1)) (m + 1)).hom h
    simpa only [push_comp_apply, FullLoopModel.include_forget, push_id_apply] using h'
  apply hi
  have hc : cocycleClass (Loops (m + 1)) _ (rep m hm F r)
      (NormalizedRelativeRepresentative.raw_closed _ _ _ _ _) = NativeGHPowers.power m r :=
    NormalizedRelativeRepresentative.raw_class _ _ _ _ _
  have hcut : (homologyPushZMod2 (LengthFilteredLoopRotation.full F (s - cutL m F r + 3 * ε)) (m + 1)).hom
      (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε (rep m hm F r)
          (NormalizedRelativeRepresentative.raw_closed _ _ _ _ _)
          (NormalizedRelativeRepresentative.raw_supported _ _ _ _ _) (a := s)).homology (m + 1)).hom
          (ThetaRaise.aligned m F r z₀)) =
      (CanonicalGlobalSelfCut.map m (NativeGHPowers.degree m r) (m + 1) (NativeGHPowers.power m r)).hom
        ((homologyPushZMod2 (LengthFilteredLoopRotation.full F s) _).hom (ThetaRaise.aligned m F r z₀)) := by
    have h := CanonicalGlobalSelfCutFiltered.original_filtered m (by omega) _ F hε (rep m hm F r)
      (NormalizedRelativeRepresentative.raw_closed _ _ _ _ _)
      (NormalizedRelativeRepresentative.raw_supported _ _ _ _ _) (m + 1) (ThetaRaise.aligned m F r z₀)
    rw [hc] at h
    exact h
  rw [hcut, ThetaRaise.aligned, ThetaRaise.push_eqToHom _ (NativeHighPowerUnitComparison.degree_match m r), hz]
  exact (NativeHighPowerUnit.single_UNIT m hm F P v₀ r).trans
    (StrictLengthFilteredUnit.candidate_full F (by omega) b hb).symm

/-- A filtered lift of the r-th Theta power just above its level. -/
theorem exists_lift (r : ℕ) :
    ∃ z₀ : homologyZMod2 (lengthSpace F (NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2))
        (NativeThetaPowers.degree m r),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F
        (NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2)) _).hom z₀ =
        NativeThetaPowers.fullPower m hm F P v₀ r :=
  NativeThetaSpectralLength.lift_above m hm F P v₀ r (by linarith)

include hm P v₀ in
/-- **The cut data of all GH powers with one unit length.** -/
theorem exists_data (hfin : (Finsler.Geodesics.primeImages F).Finite) {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hC : ∀ r : ℕ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C ≤ NativeGHSpectralSupport.level m F r) :
    ∃ (data : ∀ r : ℕ, UFHigh.CutData m F ε hε r) (Δ Bs : ℝ),
      (∀ r, (data r).s - (data r).L ≤ Δ) ∧ (∀ r, (data r).B ≤ Bs) ∧
      (∀ r, (data r).L < NativeGHSpectralSupport.level m F r ∧
        NativeGHSpectralSupport.level m F r - 1 ≤ (data r).L) := by
  set β := NativeGHOptimalRate.rate m F with hβdef
  have hβ : 0 < β := NativeGHOptimalRate.rate_positive m hm F P v₀
  set cs := β + C + 1 + 3 * ε with hcs
  obtain ⟨Ls, hLs1, -, hLsc⟩ := Finsler.ComparisonBasic.exists_regular_between (F := F) hfin (max cs 1)
  have hLs0 : 0 < Ls := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hLs1.le)
  obtain ⟨Bs, hBs, hblf⟩ := UFBLF.blf_all m F hfin hLs0 hLsc
  have hBs0 : 0 < Bs := hLs0.trans_le hBs
  have hbound : ∀ r : ℕ, NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2 - cutL m F r + 3 * ε ≤ cs := by
    intro r
    have h1 := NativeThetaGHCommonRate.theta_level_upper m hm F P v₀ r
    have h2 := hC r
    simp only [cutL]
    linarith
  choose z hz using exists_lift m hm F P v₀
  have hlev : ∀ r, NativeGHSpectralSupport.level m F r ≤ NativeThetaSpectralLength.level m hm F P v₀ r :=
    NativeThetaSpectralLength.gh_le_level m hm F P v₀
  have hsa : ∀ r, 0 < NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2 - cutL m F r + 3 * ε := by
    intro r; have := hlev r; simp only [cutL]; linarith
  have hsB : ∀ r, NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2 - cutL m F r + 3 * ε ≤ Bs :=
    fun r => (hbound r).trans (((le_max_left _ _).trans hLs1.le).trans hBs)
  have hunit : ∀ r, UFCore.enl F (hsB r) (m + 1)
      (((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε (rep m hm F r)
        (NormalizedRelativeRepresentative.raw_closed _ _ _ _ _)
        (NormalizedRelativeRepresentative.raw_supported _ _ _ _ _)
        (a := NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2)).homology (m + 1)).hom
        (ThetaRaise.aligned m F r (z r))) =
      StrictLengthFilteredUnit.candidate F (by omega) Bs hBs0 := by
    intro r
    have hcLs : NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2 - cutL m F r + 3 * ε ≤ Ls :=
      (hbound r).trans ((le_max_left _ _).trans hLs1.le)
    set cutS := ((FilteredPrismSelfCut.canonicalOperation m (NativeGHPowers.degree m r) F hε (rep m hm F r)
        (NormalizedRelativeRepresentative.raw_closed _ _ _ _ _)
        (NormalizedRelativeRepresentative.raw_supported _ _ _ _ _)
        (a := NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2)).homology (m + 1)).hom
        (ThetaRaise.aligned m F r (z r)) with hcutS
    set u := (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hcLs) (m + 1)).hom cutS with hu
    have hg : (homologyPushZMod2 (LengthFilteredLoopRotation.full F Ls) (m + 1)).hom u =
        (homologyPushZMod2 (LengthFilteredLoopRotation.full F Ls) (m + 1)).hom
          (StrictLengthFilteredUnit.candidate F (by omega) Ls hLs0) :=
      (push_comp_apply (LengthFilteredLoopRotation.cut F hcLs) (LengthFilteredLoopRotation.full F Ls) (m + 1)
        cutS).trans (cut_unit_global m hm F P v₀ r hε (z r) (hz r) Ls hLs0)
    have hd : (homologyPushZMod2 (LengthFilteredLoopRotation.full F Ls) (m + 1)).hom
        (u - StrictLengthFilteredUnit.candidate F (by omega) Ls hLs0) = 0 := by
      rw [map_sub, hg, sub_self]
    have hk := hblf (m + 1) _ hd
    rw [map_sub, sub_eq_zero, StrictLengthFilteredUnit.candidate_cut F (by omega) hLs0 hBs0 hBs] at hk
    have hk' := (push_comp_apply (LengthFilteredLoopRotation.cut F hcLs) (LengthFilteredLoopRotation.cut F hBs)
      (m + 1) cutS).symm.trans hk
    exact hk'
  refine ⟨fun r =>
    { L := cutL m F r
      s := NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2
      T := rep m hm F r
      hT := NormalizedRelativeRepresentative.raw_closed _ _ _ _ _
      hsh := NormalizedRelativeRepresentative.raw_supported _ _ _ _ _
      S := ThetaRaise.aligned m F r (z r)
      hs0 := by have := NativeThetaSpectralLength.level_positive m hm F P v₀ r; linarith
      hsa := hsa r
      B := Bs
      hB := hBs0
      hBs := hsB r
      hunit := hunit r }, β + C + 1, Bs, fun r => ?_, fun r => le_rfl, fun r => ?_⟩
  · have h1 := NativeThetaGHCommonRate.theta_level_upper m hm F P v₀ r
    have h2 := hC r
    show NativeThetaSpectralLength.level m hm F P v₀ r + 1 / 2 - cutL m F r ≤ β + C + 1
    simp only [cutL]
    linarith
  · show cutL m F r < _ ∧ _ ≤ cutL m F r
    simp only [cutL]
    constructor <;> linarith

omit hm P v₀ in
open Finsler.CriticalLevels Finsler.BorelCrossing Finsler.BorelCochain in
/-- **Uniform filling in all high degrees** with finitely many prime closed geodesic images
(length sublevels, absolute singular homology). -/
theorem uf_high (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ q₁ : ℕ, ∀ (a : ℝ) (_ha : 0 < a) (q : ℕ), q₁ ≤ q →
      ∀ x : PoolCap.homology (lengthSpace F a) q,
        (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) q).hom x = 0 →
        ∀ h : a ≤ a + D, UFCore.enl F h q x = 0 := by
  obtain ⟨P, ⟨v₀⟩⟩ := HRBridge.exists_point m
  obtain ⟨C, hC⟩ := GHSlope.gh_exact_rate m hm F P v₀ hfin
  have hε : (0 : ℝ) < 1 := one_pos
  obtain ⟨data, Δ, Bs, hΔ, hBs, hL⟩ := exists_data m hm F P v₀ hfin hε (fun r => (hC r).1)
  obtain ⟨i₀, hi₀, cmax, -, hcross⟩ := UFWindow.window_crossings m F hfin (2 * m)
  obtain ⟨D, hD, hUF⟩ := UFHigh.uf_of_data m F 1 hε hm hfin P v₀ data hΔ hBs hL hC i₀ hi₀
    (fun i hi1 hi2 b hb a' b' hab' ha' hb' h1 h2 h3 =>
      ⟨hcross i hi1 (by omega) a' b' hab' ha' h1 h2 h3,
        hcross (i + 1) (by omega) (by omega) a' b' hab' ha' h1 h2 h3⟩)
  exact ⟨D, hD, i₀ + 2 * m, hUF⟩

end

end Finsler.UFData
