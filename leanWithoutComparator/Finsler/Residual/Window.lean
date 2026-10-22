module

public import Finsler.Residual.HRBridge
public import Finsler.Loop.StrictLengthHomologyStabilization
public import Finsler.Topology.OrdinaryRestriction
public import Finsler.Topology.ComparisonBasic
public import Finsler.Topology.CrossingSlopes

/-! Injectivity above the last relevant crossing (Claude, UF prototype, piece WF).

If no single crossing above a regular cut c has ordinary cohomology in the degrees i and i + 1
(i > n + 1), a homology class of the length sublevel t_c of degree i which dies in the loop space
is zero. The ordinary restrictions between regular cuts above c are bijective in degree i
(`OrdinaryRestriction.cut_bijective_of_crossings`), hence so are the absolute singular
restrictions (singular comparison, relative-to-absolute isomorphism), hence the energy sublevel
inclusions are injective on homology (Kronecker duality over F₂: a map whose pullback is onto is
injective on homology); with the length/energy homology isomorphism and the colimit description of
the loop space homology the class dies at a regular cut already, so it is zero. -/

@[expose] public section

namespace Finsler.UFWindow

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.BorelCochain
open Finsler.SplitPairHomologyKernel

noncomputable section
set_option autoImplicit false

variable (m : ℕ) (F : ReversibleMetric (m + 1))

theorem toAbsLev_cut {a b : ℝ} (hab : a ≤ b) (i : ℕ) (y : H (levComplex F b) i) :
    HRBridge.toAbsLev m F a i (Hmap (cutHom F hab) i y) =
      (cohPullback (TopPair.Hom.fst (cutPair F hab)) i).hom (HRBridge.toAbsLev m F b i y) := by
  rw [HRBridge.toAbsLev, Finsler.BorelComparison.ordinaryEquiv_natural (revPair_sq F a) (revPair_sq F b)
    (cutPair F hab) (cutPair_equivariant F hab) i y]
  exact ConcreteCategory.congr_hom (relative_to_absolute_natural (cutPair F hab) i) _

theorem toAbsLev_surjective (a : ℝ) (i : ℕ) (hi : (m + 1) + 1 < i) :
    Function.Surjective (HRBridge.toAbsLev m F a i) := by
  intro w
  obtain ⟨v, hv⟩ := RelativeAbsoluteIso.surjective (levPair F a) i
    (ConstantLoopModel.cohomology_subsingleton (m + 1) i (by omega) (by omega)) w
  refine ⟨(Finsler.BorelComparison.ordinaryEquiv (levPair F a) (revPair F a) (revPair_sq F a) i).symm v, ?_⟩
  rw [HRBridge.toAbsLev, LinearEquiv.apply_symm_apply]
  exact hv

theorem absCut_surjective {a b : ℝ} (hab : a ≤ b) (i : ℕ) (hi : (m + 1) + 1 < i)
    (hbij : Function.Bijective (Hmap (cutHom F hab) i)) :
    Function.Surjective (cohPullback (TopPair.Hom.fst (cutPair F hab)) i).hom := by
  intro w
  obtain ⟨y, rfl⟩ := toAbsLev_surjective m F a i hi w
  obtain ⟨y', rfl⟩ := hbij.2 y
  exact ⟨HRBridge.toAbsLev m F b i y', (toAbsLev_cut m F hab i y').symm⟩

/-- Over F₂ a map whose pullback on cohomology is onto is injective on homology. -/
theorem push_injective_of_pull_surjective {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (h : Function.Surjective (cohPullback f q).hom) :
    Function.Injective (homologyPushZMod2 f q).hom := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2)]
  intro φ
  obtain ⟨a, ha⟩ := (kroneckerMap_bijective X q).2 φ
  obtain ⟨b, rfl⟩ := h a
  have hn := kroneckerMap_naturality_apply f q b
  rw [← ha, hn, LinearMap.comp_apply, hz, map_zero]

open Finsler.CriticalLevels Finsler.BorelCrossing in
/-- **WF**: above the last relevant crossing a globally null class of degree i is zero. -/
theorem window_kill (hfin : (Finsler.Geodesics.primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    (hcc : c ∉ crit F) (i : ℕ) (hi : (m + 1) + 1 < i)
    (hcr : ∀ (b : ℝ), c ≤ b → ∀ (a' b' : ℝ) (hab' : a' ≤ b'), c ≤ a' → b' ≤ b → a' ∉ crit F →
      b' ∉ crit F → (crit F ∩ Set.Icc a' b').Subsingleton →
      (∀ z : H (crossComplex F hab') i, z = 0) ∧ ∀ z : H (crossComplex F hab') (i + 1), z = 0)
    (y : homologyZMod2 (lengthSpace F c) i)
    (hy : (homologyPushZMod2 (LengthFilteredLoopRotation.full F c) i).hom y = 0) : y = 0 := by
  obtain ⟨B, hcB, hcB2, he⟩ := StrictLengthHomologyStabilization.exists_equal F i y
    (0 : homologyZMod2 (lengthSpace F c) i) (by rw [hy, map_zero])
  rw [map_zero] at he
  obtain ⟨b, hb1, -, hbc⟩ := Finsler.ComparisonBasic.exists_regular_between (F := F) hfin B
  have hBb : B ≤ b := hb1.le
  have hcb : c ≤ b := hcB.trans hBb
  have hyb : (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hcb) i).hom y = 0 := by
    have h := congrArg (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hBb) i).hom he
    rw [push_comp_apply, map_zero] at h
    exact h
  have hsq : toEnergy F c ≫ TopPair.Hom.fst (cutPair F hcb) =
      LengthFilteredLoopRotation.cut F hcb ≫ toEnergy F b := by
    ext u : 1
    rfl
  have hy' : (homologyPushZMod2 (TopPair.Hom.fst (cutPair F hcb)) i).hom
      ((homologyPushZMod2 (toEnergy F c) i).hom y) = 0 := by
    have h1 := push_comp_apply (toEnergy F c) (TopPair.Hom.fst (cutPair F hcb)) i y
    rw [hsq] at h1
    have h2 := push_comp_apply (LengthFilteredLoopRotation.cut F hcb) (toEnergy F b) i y
    have h3 : (homologyPushZMod2 (toEnergy F b) i).hom
        ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F hcb) i).hom y) = 0 := by
      rw [hyb, map_zero]
    exact h1.trans (h2.symm.trans h3)
  have hinj := push_injective_of_pull_surjective (TopPair.Hom.fst (cutPair F hcb)) i
    (absCut_surjective m F hcb i hi (Finsler.OrdinaryRestriction.cut_bijective_of_crossings F (by omega)
      hfin hc hcb hcc hbc i (hcr b hcb)))
  have hy0 : (homologyPushZMod2 (toEnergy F c) i).hom y = 0 := hinj (hy'.trans (map_zero _).symm)
  have hinv := ConcreteCategory.congr_hom (short_homology_inverse F c hc i) y
  have hinv' : (homologyPushZMod2 (toLength F c hc) i).hom
      ((homologyPushZMod2 (toEnergy F c) i).hom y) = y := by
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at hinv
    exact hinv
  rw [← hinv', hy0, map_zero]

open Finsler.CriticalLevels Finsler.BorelCrossing in
/-- **No crossing above c_max contributes in a window of degrees above the slope-0 band.** -/
theorem window_crossings (hfin : (Finsler.Geodesics.primeImages F).Finite) (w : ℕ) :
    ∃ i₀ : ℕ, (m + 1) + 1 < i₀ ∧ ∃ cmax : ℝ, 0 < cmax ∧ ∀ i : ℕ, i₀ ≤ i → i ≤ i₀ + w →
      ∀ (a' b' : ℝ) (hab' : a' ≤ b'), cmax ≤ a' → a' ∉ crit F → b' ∉ crit F →
        (crit F ∩ Set.Icc a' b').Subsingleton → ∀ z : H (crossComplex F hab') i, z = 0 := by
  classical
  obtain ⟨A, hA⟩ := Finsler.CrossingSlopes.exists_single_support F (by omega) hfin
  set S := insert (0 : ℝ) ((Finsler.CriticalCircles.labels F hfin).image (Finsler.CrossingSlopes.slope F))
  set Sp := S.filter (fun s => 0 < s)
  set smin : ℝ := if h : Sp.Nonempty then Sp.min' h else 1
  have hsmin : 0 < smin := by
    simp only [smin]
    split_ifs with h
    · exact (Finset.mem_filter.mp (Sp.min'_mem h)).2
    · exact one_pos
  have hsle : ∀ s ∈ S, 0 < s → smin ≤ s := by
    intro s hs hpos
    have hsp : s ∈ Sp := Finset.mem_filter.mpr ⟨hs, hpos⟩
    have hne : Sp.Nonempty := ⟨s, hsp⟩
    simp only [smin, hne, dite_true]
    exact Sp.min'_le s hsp
  refine ⟨max (m + 3) (A + 2), by omega, ((max (m + 3) (A + 2) + w + A + 1 : ℕ) : ℝ) / smin + 1,
    by positivity, fun i hi0 hiw a' b' hab' ha' ha'c hb'c hsub z => ?_⟩
  by_contra hz
  have ha'0 : 0 < a' := lt_of_lt_of_le (by positivity) ha'
  obtain ⟨c₀, ⟨hc₀crit, hc₀a, hc₀b⟩, s, hs, hsA⟩ :=
    hA a' b' hab' ha'0 ha'c hb'c hsub i ⟨z, hz⟩
  have hiA : (A : ℝ) + 2 ≤ i := by exact_mod_cast (show A + 2 ≤ i by omega)
  rcases lt_trichotomy s 0 with hneg | hzero | hpos
  · have : s * c₀ < 0 := mul_neg_of_neg_of_pos hneg (ha'0.trans_le hc₀a)
    have := (abs_le.mp hsA).2
    linarith
  · rw [hzero, zero_mul, sub_zero, abs_of_nonneg (by positivity)] at hsA
    linarith
  · have hsm := hsle s hs hpos
    have hc0 : ((max (m + 3) (A + 2) + w + A + 1 : ℕ) : ℝ) / smin + 1 ≤ c₀ := ha'.trans hc₀a
    have hiw' : (i : ℝ) ≤ ((max (m + 3) (A + 2) + w : ℕ) : ℝ) := by exact_mod_cast hiw
    have h1 : ((max (m + 3) (A + 2) + w + A + 1 : ℕ) : ℝ) < smin * c₀ := by
      have := (div_lt_iff₀ hsmin).mp (lt_of_lt_of_le (lt_add_one _) hc0)
      linarith
    have h2 : smin * c₀ ≤ s * c₀ := mul_le_mul_of_nonneg_right hsm (by linarith)
    have := (abs_le.mp hsA).1
    push_cast at h1 hiw'
    linarith

end

end Finsler.UFWindow
