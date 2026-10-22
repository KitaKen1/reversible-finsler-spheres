module

public import Finsler.Topology.CutFinite

/-! Invariance of the potential on intervals without critical levels. If there is no critical
level in [x, y], restriction from t_y to t_x is bijective on K-Borel cohomology, so the K-Borel
cohomology of the crossing pair vanishes. Doubling is natural for the cuts; hence restriction
between the fixed pairs of t_{2b} and t_{2a} is the composite of the root at a, the restriction
from t_b to t_a and doubling at b, and it is bijective on reflection Borel cohomology if there is
no critical level in [a, b]; so the reflection Borel cohomology of the fixed crossing pair
vanishes. Consequently, with finitely many prime closed geodesic images, the potential of every
cutoff is the same at 2a and at 2b if there is no critical level in [2a, 2b]. -/

@[expose] public section

namespace Finsler.CutRegular

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.SobolevEnergy Finsler.SobolevReflectionAction
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelFixed Finsler.BorelExact
open Finsler.BorelFreeK Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK
open Finsler.BorelCoverK Finsler.LocalCoverK Finsler.TotalExact Finsler.GradedLadder
open Finsler.FixedLadder Finsler.LadderEvent Finsler.CutPotential Finsler.CutFinite
open Finsler.CriticalLevels Finsler.FiniteCut Finsler.LocalizeK Finsler.RegularInterval

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-! ### The K-Borel crossing group -/

/-- On an interval without critical levels the K-Borel cohomology of the crossing pair
vanishes. -/
theorem crossK_eq_zero (hn : 1 ≤ n) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hreg : ∀ z ∈ Icc x y, z ∉ crit F) (q : ℕ) (c : crossK F hxy q) : c = 0 := by
  obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn x y y hx hxy le_rfl hreg
  exact sub_eq_zero_of_bijective (shortExactK (consts_subset_lev F x) (lev_mono F hxy)
    kInv_consts (kInv_lev F x) (kInv_lev F y))
    (fun p => Finsler.BorelDeformation.cut_bijective_K F hxy (toDeformationConsts D) p) q c

/-! ### The fixed crossing group -/

/-- Doubling is natural for the cuts. -/
theorem cut_dbl {a b : ℝ} (hab : a ≤ b) (hab2 : 2 * a ≤ 2 * b) :
    cutPair F hab ≫ dblPair F b =
      dblPair F a ≫ inclPair (consts_subset_fixLev F (2 * a)) (consts_subset_fixLev F (2 * b))
        subset_rfl (fixLev_mono F hab2) := by
  ext : 2 <;> rfl

/-- Restriction between the fixed pairs of t_{2b} and t_{2a} is the composite of doubling at b,
restriction from t_b to t_a and the root at a, on cochains. -/
theorem fixCut_eq {a b : ℝ} (hab : a ≤ b) (hab2 : 2 * a ≤ 2 * b) (j : ℕ)
    (x : (fixComplex F (2 * b)).C j) :
    (kHom (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a))
        (consts_subset_fixLev F (2 * b)) kInv_consts (kInv_fixLev F (2 * b)) subset_rfl
        (fixLev_mono F hab2)).φ.f j x =
      (rootHom F a).f j ((cutHom F hab).f j ((dblHom F b).f j x)) := by
  have h1 := pull_comp_apply (cutPair F hab) (dblPair F b) j x
  have h2 := pull_comp_apply (rootPair F a) (cutPair F hab ≫ dblPair F b) j x
  rw [h1] at h2
  rw [cut_dbl F hab hab2, ← Category.assoc, root_dbl, Category.id_comp] at h2
  exact h2

/-- If there is no critical level in [a, b], restriction between the fixed pairs of t_{2b} and
t_{2a} is bijective on reflection Borel cohomology. -/
theorem fixCut_bijective (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hab2 : 2 * a ≤ 2 * b) (hreg : ∀ z ∈ Icc a b, z ∉ crit F) (l : ℕ) :
    Function.Bijective (HRmap (kHom (consts_subset_fixLev F (2 * a)) kInv_consts
      (kInv_fixLev F (2 * a)) (consts_subset_fixLev F (2 * b)) kInv_consts
      (kInv_fixLev F (2 * b)) subset_rfl (fixLev_mono F hab2)).φ l) := by
  obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn a b b ha hab le_rfl hreg
  have hc := cut_bijective_of_levelDeformation F hab D l
  have e : ∀ y : HR (fixComplex F (2 * b)) l,
      HRmap (kHom (consts_subset_fixLev F (2 * a)) kInv_consts
        (kInv_fixLev F (2 * a)) (consts_subset_fixLev F (2 * b)) kInv_consts
        (kInv_fixLev F (2 * b)) subset_rfl (fixLev_mono F hab2)).φ l y =
      HRmap (rootHom F a) l (HRmap (cutHom F hab) l (HRmap (dblHom F b) l y)) := by
    intro y
    have h1 := HRmap_comp (dblHom F b) (invHomComp (cutHom F hab) (rootHom F a)) l y
    have h2 := HRmap_comp (cutHom F hab) (rootHom F a) l (HRmap (dblHom F b) l y)
    exact (HRmap_congr (fun j x => fixCut_eq F hab hab2 j x) l y).trans (h1.trans h2)
  constructor
  · intro y y' hyy
    have hyy' := (e y).symm.trans (hyy.trans (e y'))
    have h1 : HRmap (dblHom F b) l y = HRmap (dblHom F b) l y' :=
      hc.1 ((doublingEquiv F a l).injective hyy')
    exact (doublingEquiv F b l).symm.injective h1
  · intro z
    obtain ⟨v, hv⟩ := hc.2 ((doublingEquiv F a l).symm z)
    have h1 : HRmap (dblHom F b) l (doublingEquiv F b l v) = v :=
      (doublingEquiv F b l).symm_apply_apply v
    exact ⟨doublingEquiv F b l v, (e _).trans
      ((congrArg (fun t => HRmap (rootHom F a) l (HRmap (cutHom F hab) l t)) h1).trans
        ((congrArg (HRmap (rootHom F a) l) hv).trans
          ((doublingEquiv F a l).apply_symm_apply z)))⟩

/-- If there is no critical level in [a, b], the reflection Borel cohomology of the fixed
crossing pair of t_{2b} and t_{2a} vanishes. -/
theorem crossR_eq_zero (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hab2 : 2 * a ≤ 2 * b) (hreg : ∀ z ∈ Icc a b, z ∉ crit F) (l : ℕ)
    (x : crossR F hab2 l) : x = 0 :=
  sub_eq_zero_of_bijective (shortExact_incl (consts_subset_fixLev F (2 * a))
    (fixLev_mono F hab2) kInv_consts (kInv_fixLev F (2 * a)) (kInv_fixLev F (2 * b)))
    (fun p => fixCut_bijective F hn ha hab hab2 hreg p) l x

/-! ### Invariance of the potential -/

/-- With finitely many prime closed geodesic images, if there is no critical level in [2a, 2b],
the potential of every cutoff is the same at 2a and at 2b. -/
theorem cutPhi_eq_of_regular (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hreg : ∀ z ∈ Icc (2 * a) (2 * b), z ∉ crit F) (j q : ℕ) :
    cutPhi F (2 * b) j q = cutPhi F (2 * a) j q := by
  have hab2 : 2 * a ≤ 2 * b := by linarith
  have h2a : 2 * a ∉ crit F := hreg _ ⟨le_rfl, hab2⟩
  have h2b : 2 * b ∉ crit F := hreg _ ⟨hab2, le_rfl⟩
  have hreg' : ∀ z ∈ Icc a b, z ∉ crit F := fun z hz hzc =>
    hreg (2 * z) ⟨by linarith [hz.1], by linarith [hz.2]⟩ (crit_double F hzc)
  have h0a : 0 < 2 * a := by linarith
  have hb : 0 < b := by linarith
  have h0b : 0 < 2 * b := by linarith
  have hK : ∀ p, Subsingleton (crossK F hab2 p) := fun p =>
    ⟨fun c c' => (crossK_eq_zero F hn h0a hab2 hreg p c).trans
      (crossK_eq_zero F hn h0a hab2 hreg p c').symm⟩
  have hR : totRank (crossR F hab2) = 0 :=
    totRank_eq_zero (crossR F hab2) fun l x => crossR_eq_zero F hn ha hab hab2 hreg' l x
  have h1 : finrank (ZMod 2) (crossK F hab2 (q + 1)) = 0 := finrank_zero_of_subsingleton
  have h2 : finrank (ZMod 2) (crossK F hab2 (q + 1 + 1)) = 0 := finrank_zero_of_subsingleton
  have h := cutPhi_near F hab2 j q (finTot_fixR F hn hfin ha h2a) (finTot_fixR F hn hfin hb h2b)
    (finTot_crossR F hn hfin ha hab2 h2a h2b) (finite_HK F hn hfin h0a h2a q)
    (finite_HK F hn hfin h0a h2a (q + 1)) (finite_HK F hn hfin h0b h2b (q + 1))
    (finite_crossK F hn hfin h0a hab2 h2a h2b (q + 1))
    (finite_crossK F hn hfin h0a hab2 h2a h2b (q + 1 + 1)) (M := 0) hR.le h1.le h2.le
  rw [Nat.cast_zero, mul_zero, add_zero, add_zero] at h
  exact le_antisymm h.1 h.2

end

end Finsler.CutRegular
