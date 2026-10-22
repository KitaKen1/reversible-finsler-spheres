module

public import Finsler.Geometry.RoundEven
public import Finsler.Topology.KLift
public import Finsler.Geometry.RoundECompat
public import Finsler.Topology.CrossingWK

/-! **G6b (`YTop`) for the round sphere**: at the odd stages j the e-multiple of the start class
lifts to K-Borel cohomology.

At the odd stages the critical level 2πm has m = j + 1 even, and near its critical loops the
averaged evaluation ẽ = normalize(u(0) + u(1/2)) is defined, invariant under the reversal and
the half rotation, and never antipodal to the evaluation at 0 (`RoundEven`). On the lens pair of
a local lens compatible with the half rotation (tight cuts a' < 2πm < b') the K-Borel cup with
ẽ^*[Sⁿ] lifts the multiples of the evaluation class (`KLift.good_of_invariant`, then the straight
homotopy ẽ ≃ ev₀). These K-lifted multiples pass along excision to (t_{b'}, Y), along the lens
retraction to (t_{b'}, t_{a'}), and along the level deformations to the wide crossing
(t_b, t_a) (`KLift.good_pull`, `KLift.good_push`). For the start class τ, lifted to K-Borel
cohomology in its lowest degree (`GlobalK.fgtR_low`), the K-class obtained is forgotten to the
class of e·τ in actual relative cohomology; forgetting is injective in its degree (the Gysin
pattern), so it is forgotten to e·τ in reflection Borel cohomology. -/

@[expose] public section

namespace Finsler.RoundYTop

open CategoryTheory Set Topology SphereOddDegree
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelDeformation Finsler.AvoidPoint Finsler.BorelLens
open Finsler.BorelLocal Finsler.BorelIterate Finsler.BorelK Finsler.BorelCrossingK
open Finsler.BorelLocalK Finsler.RegularInterval Finsler.OrientedCritical Finsler.CriticalLevels
open Finsler.RoundEven Finsler.KLift Finsler.BasisBudget Finsler.BorelGraded
open Finsler.RoundFiltration Finsler.RoundCrossPattern Finsler.RoundKGlobal Finsler.GysinPattern
open Finsler.RoundRGlobal
open scoped Real

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### The evaluation class on sets of loops -/

/-- The evaluation class on a set of loops. -/
def eT (hn : 1 ≤ n) (t : Set (Loops n)) : cohomologyZMod2 (TopCat.of t) n :=
  (cohPullback (evT t) n).hom (Finsler.SphereTopClass.topClass n hn)

theorem pull_comp_eq {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    {q : ℕ} (a : cohomologyZMod2 Z q) :
    (cohPullback f q).hom ((cohPullback g q).hom a) = (cohPullback h q).hom a := by
  rw [← Finsler.Cup.pullback_comp, hfg]

theorem pull_eT (hn : 1 ≤ n) {t t' : Set (Loops n)} (g : TopCat.of t ⟶ TopCat.of t')
    (hg : g ≫ evT t' = evT t) : (cohPullback g n).hom (eT hn t') = eT hn t :=
  pull_comp_eq g (evT t') (evT t) hg _

/-! ### K-lifted multiples on pairs of invariant sets of loops -/

section Sub

variable (hn : 1 ≤ n) {s t : Set (Loops n)} (hst : s ⊆ t)
  (hs : ∀ u : SphereLoop n, u ∈ s → reverseSphere u ∈ s)
  (ht : ∀ u : SphereLoop n, u ∈ t → reverseSphere u ∈ t)
  (hhs : ∀ u : SphereLoop n, u ∈ s → half +ᵥ u ∈ s)
  (hht : ∀ u : SphereLoop n, u ∈ t → half +ᵥ u ∈ t)

/-- K-lifted multiples of the evaluation class on a pair of invariant sets of loops. -/
def GoodSub (l : ℕ) : Prop :=
  Good (revSub_sq hst hs ht) (halfSub_sq hst hhs hht) (halfSub_rev hst hs ht hhs hht) (eT hn t) l

variable {s' t' : Set (Loops n)} (hst' : s' ⊆ t')
  (hs' : ∀ u : SphereLoop n, u ∈ s' → reverseSphere u ∈ s')
  (ht' : ∀ u : SphereLoop n, u ∈ t' → reverseSphere u ∈ t')
  (hhs' : ∀ u : SphereLoop n, u ∈ s' → half +ᵥ u ∈ s')
  (hht' : ∀ u : SphereLoop n, u ∈ t' → half +ᵥ u ∈ t')
  (hss : s ⊆ s') (htt : t ⊆ t')

theorem incl_evT : TopPair.Hom.fst (inclPair hst hst' hss htt) ≫ evT t' = evT t := rfl

/-- Pulling back K-lifted multiples along an inclusion onto in degree l. -/
theorem goodSub_pull (l : ℕ)
    (hsurj : Function.Surjective (HRmap (borelHom
      (subCommHom hst hs ht hhs hht hst' hs' ht' hhs' hht' hss htt)) l))
    (h : GoodSub hn hst' hs' ht' hhs' hht' l) : GoodSub hn hst hs ht hhs hht l := by
  have h' := good_pull (revSub_sq hst hs ht) (revSub_sq hst' hs' ht') (inclPair hst hst' hss htt)
    (inclPair_equivariant hst hst' hs ht hs' ht' hss htt) (halfSub_sq hst hhs hht)
    (halfSub_sq hst' hhs' hht') (halfSub_rev hst hs ht hhs hht)
    (halfSub_rev hst' hs' ht' hhs' hht') (inclPair_half hst hhs hht hst' hhs' hht' hss htt)
    (eT hn t') hsurj h
  exact good_congr _ _ _ h' (pull_eT hn _ (incl_evT hst hst' hss htt))

/-- Pushing forward K-lifted multiples along an inclusion which is an isomorphism on actual
relative cohomology. -/
theorem goodSub_push (l : ℕ)
    (hbij : ∀ k, Function.Bijective (nativePull (inclPair hst hst' hss htt) k))
    (h : GoodSub hn hst hs ht hhs hht l) : GoodSub hn hst' hs' ht' hhs' hht' l := by
  refine good_push (revSub_sq hst hs ht) (revSub_sq hst' hs' ht') (inclPair hst hst' hss htt)
    (inclPair_equivariant hst hst' hs ht hs' ht' hss htt) (halfSub_sq hst hhs hht)
    (halfSub_sq hst' hhs' hht') (halfSub_rev hst hs ht hhs hht)
    (halfSub_rev hst' hs' ht' hhs' hht') (inclPair_half hst hhs hht hst' hhs' hht' hss htt)
    (eT hn t') (bijective_subCommHom hst hs ht hhs hht hst' hs' ht' hhs' hht' hss htt hbij (n + l)).2
    (hbij (n + l)).1 (good_congr _ _ _ h (pull_eT hn _ (incl_evT hst hst' hss htt)).symm)

variable (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) (hsa : s ⊆ lev F a) (htb : t ⊆ lev F b)

/-- K-lifted multiples of the evaluation class on a crossing pair. -/
def GoodCross (l : ℕ) : Prop :=
  Good (revCross_sq F hab) (halfCross_sq F hab) (halfCross_rev F hab)
    ((cohPullback (crossEval F hab) n).hom (Finsler.SphereTopClass.topClass n hn)) l

theorem cross_evT : TopPair.Hom.fst (toCross hst F hab hsa htb) ≫ crossEval F hab = evT t := rfl

/-- Pulling back K-lifted multiples from a crossing pair. -/
theorem goodCross_pull (l : ℕ)
    (hsurj : Function.Surjective (HRmap (borelHom
      (toCrossCommHom hst hs ht hhs hht F hab hsa htb)) l))
    (h : GoodCross hn F hab l) : GoodSub hn hst hs ht hhs hht l := by
  have h' := good_pull (revSub_sq hst hs ht) (revCross_sq F hab) (toCross hst F hab hsa htb)
    (toCross_equivariant hst hs ht F hab hsa htb) (halfSub_sq hst hhs hht) (halfCross_sq F hab)
    (halfSub_rev hst hs ht hhs hht) (halfCross_rev F hab)
    (toCross_half hst hhs hht F hab hsa htb) _ hsurj h
  exact good_congr _ _ _ h' (pull_comp_eq _ _ _ (cross_evT hst F hab hsa htb) _)

/-- Pushing forward K-lifted multiples to a crossing pair. -/
theorem goodCross_push (l : ℕ)
    (hbij : ∀ k, Function.Bijective (nativePull (toCross hst F hab hsa htb) k))
    (h : GoodSub hn hst hs ht hhs hht l) : GoodCross hn F hab l := by
  refine good_push (revSub_sq hst hs ht) (revCross_sq F hab) (toCross hst F hab hsa htb)
    (toCross_equivariant hst hs ht F hab hsa htb) (halfSub_sq hst hhs hht) (halfCross_sq F hab)
    (halfSub_rev hst hs ht hhs hht) (halfCross_rev F hab)
    (toCross_half hst hhs hht F hab hsa htb) _
    (bijective_toCrossCommHom hst hs ht hhs hht F hab hsa htb hbij (n + l)).2 (hbij (n + l)).1
    (good_congr _ _ _ h (pull_comp_eq _ _ _ (cross_evT hst F hab hsa htb) _).symm)

end Sub

/-! ### The lens pair -/

section Lens

variable (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) (he : Even m) {a b : ℝ}
  (L : LocalLens (roundMetric n) a b (tube (roundMetric n) (2 * π * m) (1 / 4)))
  (hL : HalfLens (roundMetric n) L)

include hm he in
theorem lens_sumH : ∀ u : SphereLoop n, u ∈ L.N ∩ lev (roundMetric n) b → sumH u ≠ 0 :=
  fun _ hu => tube_sumH_ne hm he (L.inside hu)

include hm he in
/-- **On the lens pair the multiples of the evaluation class lift** (the K-Borel cup with the
averaged evaluation). -/
theorem good_lens (l : ℕ) :
    GoodSub hn (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩) l := by
  have h := good_of_invariant
    (revSub_sq (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩))
    (halfSub_sq (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩))
    (halfSub_rev (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩))
    (evH _ (lens_sumH hm he L))
    (evH_rev (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩) (lens_sumH hm he L))
    (evH_half (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩) (lens_sumH hm he L))
    (Finsler.SphereTopClass.topClass n hn) l
  exact good_congr _ _ _ h (Finsler.ECup.pullback_eq_of_ne_neg (evH _ (lens_sumH hm he L)) (evT _)
    (evT_ne_neg _ (lens_sumH hm he L)) _)

end Lens

/-! ### The wide crossing -/

/-- **On the round crossings of even order the multiples of the evaluation class lift to K-Borel
cohomology.** -/
theorem good_cross (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) (he : Even m) {a b : ℝ}
    (hlo : 2 * π * ((m : ℝ) - 1) < a) (hac : a < 2 * π * m) (hcb : 2 * π * m < b)
    (hhi : b < 2 * π * ((m : ℝ) + 1)) (hab : a ≤ b) (l : ℕ) :
    GoodCross hn (roundMetric n) hab l := by
  have hπ := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc0 : 0 < 2 * π * m := by positivity
  have ha : 0 < a := by
    have h0 : 0 ≤ 2 * π * ((m : ℝ) - 1) := by
      have : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
      positivity
    linarith
  obtain ⟨ε, hε, hLs⟩ := CrossingWK.halfLens_of_shortening (roundMetric n) hc0
    (tube (roundMetric n) (2 * π * m) (1 / 4))
    (ShorteningK.exists_near_half (roundMetric n) hn hc0 (by norm_num))
  obtain ⟨a', ha'1, ha'2⟩ := exists_between (max_lt hac (sub_lt_self (2 * π * m) hε))
  obtain ⟨b', hb'1, hb'2⟩ := exists_between (lt_min hcb (lt_add_of_pos_right (2 * π * m) hε))
  have haa : a ≤ a' := (le_max_left _ _).trans ha'1.le
  have hbb : b' ≤ b := hb'2.le.trans (min_le_left _ _)
  have hab' : a' ≤ b' := (ha'2.trans hb'1).le
  have hreg₁ : ∀ x ∈ Icc a a', x ∉ crit (roundMetric n) := by
    intro x hx hxc
    obtain ⟨k, -, rfl⟩ := Finsler.RoundCrossW.crit_round hxc
    have h1 : (m : ℝ) - 1 < k := lt_of_mul_lt_mul_left (hlo.trans_le hx.1) (by positivity)
    have h2 : (k : ℝ) < m := lt_of_mul_lt_mul_left (hx.2.trans_lt ha'2) (by positivity)
    have e1 : m < k + 1 := by exact_mod_cast (show (m : ℝ) < k + 1 by linarith)
    have e2 : k < m := by exact_mod_cast h2
    omega
  have hreg₂ : ∀ x ∈ Icc b' b, x ∉ crit (roundMetric n) := by
    intro x hx hxc
    obtain ⟨k, -, rfl⟩ := Finsler.RoundCrossW.crit_round hxc
    have h1 : (m : ℝ) < k := lt_of_mul_lt_mul_left (hb'1.trans_le hx.1) (by positivity)
    have h2 : (k : ℝ) < m + 1 := lt_of_mul_lt_mul_left (hx.2.trans_lt hhi) (by positivity)
    have e1 : m < k := by exact_mod_cast h1
    have e2 : k < m + 1 := by exact_mod_cast h2
    omega
  obtain ⟨D₁⟩ := CrossingW.levelDeformation_of_regular (roundMetric n) hn a a' b' ha haa hab'
    hreg₁
  obtain ⟨D₂⟩ := CrossingW.levelDeformation_of_regular (roundMetric n) hn b' b b
    (ha.trans_le (haa.trans hab')) hbb le_rfl hreg₂
  obtain ⟨L, hL⟩ := hLs a' b' ((le_max_right _ _).trans_lt ha'1) ha'2 hb'1
    (hb'2.trans_le (min_le_right _ _))
  have hra : ∀ u : SphereLoop n, u ∈ lev (roundMetric n) a →
      reverseSphere u ∈ lev (roundMetric n) a := fun _ hu => reverse_mem_lev _ hu
  have hra' : ∀ u : SphereLoop n, u ∈ lev (roundMetric n) a' →
      reverseSphere u ∈ lev (roundMetric n) a' := fun _ hu => reverse_mem_lev _ hu
  have hrb' : ∀ u : SphereLoop n, u ∈ lev (roundMetric n) b' →
      reverseSphere u ∈ lev (roundMetric n) b' := fun _ hu => reverse_mem_lev _ hu
  have hha : ∀ u : SphereLoop n, u ∈ lev (roundMetric n) a →
      half +ᵥ u ∈ lev (roundMetric n) a := fun _ hu => half_mem_lev _ hu
  have hha' : ∀ u : SphereLoop n, u ∈ lev (roundMetric n) a' →
      half +ᵥ u ∈ lev (roundMetric n) a' := fun _ hu => half_mem_lev _ hu
  have hhb' : ∀ u : SphereLoop n, u ∈ lev (roundMetric n) b' →
      half +ᵥ u ∈ lev (roundMetric n) b' := fun _ hu => half_mem_lev _ hu
  -- the lens pair
  have G5 := good_lens hn hm he L hL l
  -- excision to (t_{b'}, Y)
  have G4 := goodSub_push hn (inter_subset_inter_right L.N L.subset_lev)
    (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
    (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩)
    (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
    (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩) L.subset_lev L.Y_rev hrb' hL.Y_half hhb'
    inter_subset_right inter_subset_right l
    (fun k => bijective_nativePull_excision L.N L.subset_lev L.Y_open L.N_open L.cover k) G5
  -- the lens retraction: (t_{b'}, t_{a'})
  have G3 := goodSub_pull hn (L.lev_subset.trans L.subset_lev) hra' hrb' hha' hhb' L.subset_lev
    L.Y_rev hrb' hL.Y_half hhb' L.lev_subset subset_rfl l (halfLens_surjective _ L hL l) G4
  -- the tight crossing
  have G3' := goodCross_push hn (L.lev_subset.trans L.subset_lev) hra' hrb' hha' hhb'
    (roundMetric n) hab' subset_rfl subset_rfl l
    (fun k => bijective_nativePull_of_eq (lev_mono _ hab') (lev_mono _ hab') subset_rfl subset_rfl
      subset_rfl subset_rfl k) G3
  -- the level deformation below: (t_{b'}, t_a)
  have G2 := goodCross_pull hn (lev_mono (roundMetric n) (haa.trans hab')) hra hrb' hha hhb'
    (roundMetric n) hab' (lev_mono _ haa) subset_rfl l
    (bijective_toCrossCommHom (lev_mono (roundMetric n) (haa.trans hab')) hra hrb' hha hhb'
      (roundMetric n) hab' (lev_mono _ haa) subset_rfl
      (fun k => bijective_nativePull_inclPair (lev_mono (roundMetric n) (haa.trans hab'))
        (lev_mono _ hab') (lev_mono _ haa) subset_rfl (toPairDeformation D₁) k) l).2 G3'
  -- the level deformation above: the wide crossing
  exact goodCross_push hn (lev_mono (roundMetric n) (haa.trans hab')) hra hrb' hha hhb'
    (roundMetric n) hab subset_rfl (lev_mono _ hbb) l
    (fun k => bijective_nativePull (lev_mono (roundMetric n) (haa.trans hab')) (lev_mono _ hbb)
      (toDeformation D₂ a) k) G2

/-! ### G6b -/

/-- The forgotten class of e·τ on a crossing pair. -/
theorem forgetNative_crossE (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) (hn : 1 ≤ n) (q : ℕ)
    (τ : HR (crossComplex F hab) q) :
    forgetNative (crossPair F hab) (revCross F hab) (revCross_sq F hab) (n + q)
        (crossE F hab hn q τ) =
      Finsler.RelativeCup.cup (crossPair F hab) n q
        ((cohPullback (crossEval F hab) n).hom (Finsler.SphereTopClass.topClass n hn))
        (forgetNative (crossPair F hab) (revCross F hab) (revCross_sq F hab) q τ) := by
  have hf := BorelCup.cup_forgetNative (crossPair F hab) (revCross F hab) (revCross_sq F hab) n
    (cochainPullback (crossEval F hab) n
      (classRepr (Finsler.BorelEvaluation.sphere n) n (Finsler.SphereTopClass.topClass n hn)))
    (cochainPullback_cocycle _ _ _ (classRepr_isCocycle (Finsler.BorelEvaluation.sphere n) n
      (Finsler.SphereTopClass.topClass n hn)))
    (Finsler.BorelEvaluation.cochain_invariant _ _ (crossEval_invariant F hab) n _) q τ
  have h1 := cohPullback_cocycleClass (crossEval F hab) n
    (classRepr (Finsler.BorelEvaluation.sphere n) n (Finsler.SphereTopClass.topClass n hn))
    (classRepr_isCocycle (Finsler.BorelEvaluation.sphere n) n (Finsler.SphereTopClass.topClass n hn))
  rw [cocycleClass_classRepr] at h1
  rw [h1]
  exact hf

theorem fgtR_castHR {K : InvComplex} (S : Commuting K) {a b : ℕ} (h : a = b)
    (y : HR (borelInv S) a) : fgtR S b (castHR h y) = castHR h (fgtR S a y) := by
  subst h
  rfl

theorem injective_forget_cast {K : InvComplex} {a b : ℕ} (h : a = b)
    (hinj : Function.Injective (forget K a)) : Function.Injective (forget K b) := by
  subst h
  exact hinj

/-- **G6b for the round sphere**: at the odd stages the e-multiple of the start class lifts to
K-Borel cohomology. -/
theorem ytop (hn : 3 ≤ n) : YTop n hn := by
  intro j hj
  have hn1 : 1 ≤ n := by omega
  have hτ := startClass_ne hn j
  have hE := Finsler.RoundECompat.ecompat hn j (startClass hn j) hτ
  let A := roundPattern (by omega) (show 0 < j + 1 by omega) (cut_lo j) (cut_ac j) (cut_cb j) (cut_hi j)
    (cut_mono j) (startClass hn j) hτ hE
  obtain ⟨τK, hτK⟩ :=
    (Finsler.GlobalK.fgtR_low (halfCommutingCross (roundMetric n) (cut_mono j)) A).1
      (startClass hn j)
  obtain ⟨y₀, hy₀⟩ := good_cross hn1 (show 0 < j + 1 by omega) hj.add_one (cut_lo j) (cut_ac j) (cut_cb j)
    (cut_hi j) (cut_mono j) (lc n (j + 1)) τK
  refine ⟨castHR (degE hn _) y₀, ?_⟩
  rw [fgtR_castHR]
  congr 1
  have hinj : Function.Injective
      (forget (crossComplex (roundMetric n) (cut_mono j)) (n + lc n (j + 1))) :=
    injective_forget_cast (show lc n (j + 1) + (n - 1) + 1 = n + lc n (j + 1) by omega)
      (forget_injective_of_w_zero _ _ (Pattern.w_zero_bottom_top A))
  apply hinj
  apply (ordinaryEquiv (crossPair (roundMetric n) (cut_mono j)) (revCross (roundMetric n) (cut_mono j))
    (revCross_sq (roundMetric n) (cut_mono j)) _).injective
  calc _ = fN (revCross_sq (roundMetric n) (cut_mono j)) (halfCross_sq (roundMetric n) (cut_mono j))
        (halfCross_rev (roundMetric n) (cut_mono j)) (n + lc n (j + 1)) y₀ := rfl
    _ = _ := hy₀
    _ = Finsler.RelativeCup.cup (crossPair (roundMetric n) (cut_mono j)) n (lc n (j + 1))
          ((cohPullback (crossEval (roundMetric n) (cut_mono j)) n).hom
            (Finsler.SphereTopClass.topClass n hn1))
          (forgetNative (crossPair (roundMetric n) (cut_mono j)) (revCross (roundMetric n) (cut_mono j))
            (revCross_sq (roundMetric n) (cut_mono j)) (lc n (j + 1)) (startClass hn j)) := by
      rw [fN_apply]
      exact congrArg _ (congrArg _ hτK)
    _ = _ := (forgetNative_crossE (roundMetric n) (cut_mono j) hn1 (lc n (j + 1))
          (startClass hn j)).symm

/-- **The global basis of the round sphere (stage 13)**, with no remaining hypothesis. -/
def stage13 (hn : 3 ≤ n) : Finsler.BasisBudget.Data n (by omega) :=
  Finsler.RoundECompat.stage13DataY hn (ytop hn)

/-- **The global basis exists** for every n ≥ 3: the reflection Borel cohomology of the loop space
pair has the graded basis of bottoms, odd tops and their w-multiples, with the required K-lifts. -/
theorem nonempty_basis (hn : 3 ≤ n) : Nonempty (Finsler.BasisBudget.Data n (by omega)) :=
  ⟨stage13 hn⟩

/-- **w^n = 0** on the reflection Borel cohomology of the loop space pair, for every n ≥ 3. -/
theorem basis_w_nil (hn : 3 ≤ n) (lo : ℕ) (x : HR (fullComplex n) lo) :
    Finsler.NilpotentW.wPow (fullComplex n) lo n x = 0 :=
  Finsler.RoundECompat.round_w_nil_uncond hn lo x

end

end Finsler.RoundYTop
