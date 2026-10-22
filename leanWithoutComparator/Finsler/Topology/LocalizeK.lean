module

public import Finsler.Topology.LocalCoverK
public import Finsler.Topology.TripleK
public import Finsler.Topology.TrivialK
public import Finsler.Topology.CutCount

/-! High-degree localization at the loops fixed by the half rotation, and the doubling rank
formula. On the fixed loops of a sublevel the half rotation acts as the identity on cochains,
so their K-Borel cohomology relative to the constant loops is the product of the reflection
Borel cohomology groups, which doubling identifies with those of (t_a, M). For the triple of
the constant loops, the fixed loops of t_{2a} and t_{2a}, at a regular cut 2a with finitely many
prime closed geodesic images: the reflection Borel cohomology of (t_{2a}, M) and of the fixed
pair vanishes in high degrees, powers of the reflection class vanish on their K-Borel
cohomology, and a power of U = v(v + w) vanishes on the K-Borel cohomology of t_{2a} relative to
its fixed loops. Hence restriction from (t_{2a}, M) to the fixed pair is bijective on K-Borel
cohomology in high degrees, the stable dimension of the K-Borel cohomology of (t_{2a}, M) is
the total dimension of the reflection Borel cohomology B_a of (t_a, M), and

  dim B_{2a} = dim B_a + 2 · dim ker(v on the K-Borel cohomology of (t_{2a}, M)). -/

@[expose] public section

namespace Finsler.LocalizeK

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelFixed Finsler.CriticalLevels
open Finsler.AvoidPoint Finsler.BorelLocalK Finsler.BorelCoverK Finsler.NilpotentW
open Finsler.NilpotentWK Finsler.FiniteCut Finsler.CutCount Finsler.LocalCoverK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (F : ReversibleMetric n)

/-! ### The fixed pair -/

/-- The two commuting involutions on the reflection cochains of the fixed pair, in the form used
for pairs of invariant sets of loops. -/
def fixCommuting (b : ℝ) : Commuting (fixComplex F b) :=
  kCommuting (consts_subset_fixLev F b) kInv_consts (kInv_fixLev F b)

/-- The two commuting involutions on the reflection cochains of (t_b, M), in the form used for
pairs of invariant sets of loops, are those of the K-Borel cochains. -/
theorem kCommuting_lev (b : ℝ) :
    kCommuting (consts_subset_lev F b) kInv_consts (kInv_lev F b) = halfCommuting F b := rfl

/-- The half rotation acts as the identity on the cochains of the fixed pair. -/
theorem fixCommuting_trivial (b : ℝ) : ∀ j x, (fixCommuting F b).s j x = x := by
  intro j x
  have h : halfSet (kInv_fixLev F b).half_mem = ContinuousMap.id (fixLev F b) := by
    ext u
    exact ((mem_fixLev_iff F b _).mp u.2).2
  have e : halfSub (consts_subset_fixLev F b) (kInv_consts (n := n)).half_mem
      (kInv_fixLev F b).half_mem = 𝟙 (pairOf (consts_subset_fixLev F b)) :=
    (pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _)
  change ((pull (halfSub (consts_subset_fixLev F b) (kInv_consts (n := n)).half_mem
    (kInv_fixLev F b).half_mem)).f j).hom x = x
  rw [e]
  exact pull_id_apply _ j x

/-- The reflection Borel cohomology of the fixed pair at 2a vanishes where that of (t_a, M)
does. -/
theorem HR_fix_eq_zero {a : ℝ} {Q : ℕ}
    (hz : ∀ q, Q ≤ q → ∀ x : HR (levComplex F a) q, x = 0) (q : ℕ) (hq : Q ≤ q)
    (x : HR (fixComplex F (2 * a)) q) : x = 0 := by
  apply (doublingEquiv F a q).symm.injective
  exact (hz q hq _).trans (hz q hq _).symm

/-- A power of w vanishing on the reflection Borel cohomology of (t_a, M) vanishes on that of
the fixed pair at 2a. -/
theorem wPow_fix_eq_zero {a : ℝ} {M : ℕ}
    (hw : ∀ (lo : ℕ) (x : HR (levComplex F a) lo), wPow (levComplex F a) lo M x = 0) (lo : ℕ)
    (x : HR (fixComplex F (2 * a)) lo) : wPow (fixComplex F (2 * a)) lo M x = 0 := by
  apply (doublingEquiv F a (lo + M)).symm.injective
  have h : HRmap (dblHom F a) (lo + M) (wPow (fixComplex F (2 * a)) lo M x) = 0 := by
    rw [HRmap_wPow, hw]
  exact h.trans (map_zero (HRmap (dblHom F a) (lo + M))).symm

/-! ### Localization -/

/-- High-degree localization: with finitely many prime closed geodesic images, at a regular cut
2a restriction from (t_{2a}, M) to the pair of its loops fixed by the half rotation is bijective
on K-Borel cohomology in high degrees. -/
theorem exists_bijective_fixed (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q : ℕ, ∀ q, Q ≤ q → Function.Bijective (HRmap (borelHom
      (kHom (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a))
        ((consts_subset_fixLev F (2 * a)).trans (fixLev_subset_lev F (2 * a))) kInv_consts
        (kInv_lev F (2 * a)) subset_rfl (fixLev_subset_lev F (2 * a)))) q) := by
  have hac : a ∉ crit F := fun h => h2a (crit_double F h)
  have h2 : 0 < 2 * a := by linarith
  obtain ⟨Q₂, -, hz2⟩ := exists_finite_HR F hn hfin h2 h2a
  obtain ⟨Q₁, -, hz1⟩ := exists_finite_HR F hn hfin ha hac
  obtain ⟨M₁, hW⟩ := exists_innerW_nilpotent F hn hfin (2 * a) h2 h2a
  obtain ⟨M₂, hw⟩ := exists_w_nilpotent F hn hfin a ha hac
  obtain ⟨d⟩ := Finsler.HalfDeform.exists_data_of_regular F hn hfin h2 h2a
  obtain ⟨k, hU⟩ := exists_ann_fixed h2 d
  have hW'' : ∀ (lo : ℕ) (x : HR (borelInv (fixCommuting F (2 * a))) lo),
      innerPow (fixCommuting F (2 * a)) lo M₂ x = 0 :=
    Finsler.TrivialK.innerPow_eq_zero_of_trivial (fixCommuting F (2 * a))
      (fixCommuting_trivial F (2 * a)) (wPow_fix_eq_zero F hw)
  refine ⟨max Q₁ Q₂ + 1, fun q hq => ?_⟩
  exact Finsler.TripleK.bijective_of_nilpotent
    (kHom ((consts_subset_fixLev F (2 * a)).trans (fixLev_subset_lev F (2 * a))) kInv_consts
      (kInv_lev F (2 * a)) (fixLev_subset_lev F (2 * a)) (kInv_fixLev F (2 * a))
      (kInv_lev F (2 * a)) (consts_subset_fixLev F (2 * a)) subset_rfl)
    (kHom (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a))
      ((consts_subset_fixLev F (2 * a)).trans (fixLev_subset_lev F (2 * a))) kInv_consts
      (kInv_lev F (2 * a)) subset_rfl (fixLev_subset_lev F (2 * a)))
    (shortExact_incl (consts_subset_fixLev F (2 * a)) (fixLev_subset_lev F (2 * a)) kInv_consts
      (kInv_fixLev F (2 * a)) (kInv_lev F (2 * a)))
    (Q := max Q₁ Q₂)
    (fun q hq x => hz2 q ((le_max_right Q₁ Q₂).trans hq) x)
    (fun q hq x => HR_fix_eq_zero F hz1 q ((le_max_left Q₁ Q₂).trans hq) x)
    hW hW'' hU q hq

/-- The stable dimension of the K-Borel cohomology of (t_{2a}, M) is the total dimension of the
reflection Borel cohomology of (t_a, M). -/
theorem exists_finrank_HK_double (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : 0 < a) (h2a : 2 * a ∉ crit F) :
    ∃ Q : ℕ, ∀ q, Q ≤ q → finrank (ZMod 2) (HK F (2 * a) q) =
      ∑ l ∈ Finset.range (q + 1), finrank (ZMod 2) (HR (levComplex F a) l) := by
  have hac : a ∉ crit F := fun h => h2a (crit_double F h)
  obtain ⟨Q, hbij⟩ := exists_bijective_fixed F hn hfin ha h2a
  obtain ⟨_, hfinR, -⟩ := exists_finite_HR F hn hfin ha hac
  have hfix : ∀ l, Module.Finite (ZMod 2) (HR (fixComplex F (2 * a)) l) := fun l => by
    have := hfinR l
    exact Module.Finite.equiv (doublingEquiv F a l)
  refine ⟨Q, fun q hq => ?_⟩
  have e1 : finrank (ZMod 2) (HK F (2 * a) q) =
      finrank (ZMod 2) (HR (borelInv (fixCommuting F (2 * a))) q) :=
    (LinearEquiv.ofBijective _ (hbij q hq)).finrank_eq
  have e2 := Finsler.TrivialK.finrank_trivial (fixCommuting F (2 * a))
    (fixCommuting_trivial F (2 * a)) q
  rw [e1, e2]
  exact Finset.sum_congr rfl fun l _ => (doublingEquiv F a l).finrank_eq.symm

/-- The doubling rank formula: with finitely many prime closed geodesic images, at a regular cut
2a the total dimension of the reflection Borel cohomology of (t_{2a}, M) is that of (t_a, M)
plus twice the total dimension of the kernel of v on the K-Borel cohomology of (t_{2a}, M). -/
theorem exists_doubling_count (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q →
      ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (HR (levComplex F (2 * a)) q) =
        ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (HR (levComplex F a) q) +
          2 * ∑ q ∈ Finset.range (Q + 1),
            finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) := by
  have h2 : 0 < 2 * a := by linarith
  obtain ⟨Q₁, -, -, hcount⟩ := exists_count_K F hn hfin h2 h2a
  obtain ⟨Q₂, hρ⟩ := exists_finrank_HK_double F hn hfin ha h2a
  refine ⟨max Q₁ Q₂, fun Q hQ => ?_⟩
  rw [hcount Q ((le_max_left Q₁ Q₂).trans hQ), hρ Q ((le_max_right Q₁ Q₂).trans hQ)]

end

end Finsler.LocalizeK
