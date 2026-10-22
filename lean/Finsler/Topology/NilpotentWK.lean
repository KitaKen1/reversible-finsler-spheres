module

public import Finsler.Topology.CrossingWK
public import Finsler.Topology.NilpotentW

/-! Nilpotence of the reflection class on K-Borel cohomology at finite cuts. The k-fold power of
the reflection class on the Borel cohomology of an iterated complex is natural for maps
commuting with the second involutions. A power of the
reflection class vanishing at the lower cut vanishes at the upper cut if restriction is
injective; if the reflection class acts as zero on the K-Borel cohomology of the crossing pair,
a k-th power vanishing at the lower cut gives a (k+1)-st power vanishing at the upper cut, by
exactness of the K-Borel crossing sequence. With finitely many prime closed geodesic images,
the K-Borel cohomology of small sublevels vanishes and some power of the reflection class
vanishes on the K-Borel cohomology of (t_a, M) at every regular cut a > 0. -/

@[expose] public section

namespace Finsler.NilpotentWK

open Set
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.BorelCochain Finsler.CriticalLevels Finsler.RegularInterval
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelCrossingK Finsler.BorelFreeK

noncomputable section

section Algebra

variable {K L : InvComplex} (S : Commuting K)

/-- The k-fold power of the reflection class on the Borel cohomology of the iterated complex,
from degree lo. -/
def innerPow (lo k : ℕ) : HR (borelInv S) lo → HR (borelInv S) (lo + k) :=
  Finsler.Gysin.word (V := fun i => HR (borelInv S) (lo + i))
    (fun i => (innerStep S (lo + i)).toAddMonoidHom) k

theorem innerPow_zero (lo : ℕ) (x : HR (borelInv S) lo) : innerPow S lo 0 x = x := rfl

theorem innerPow_succ (lo k : ℕ) (x : HR (borelInv S) lo) :
    innerPow S lo (k + 1) x = innerStep S (lo + k) (innerPow S lo k x) := rfl

variable {SK : Commuting K} {SL : Commuting L} (Φ : CommHom SK SL)

/-- Powers of the reflection class are natural. -/
theorem HRmap_innerPow (lo k : ℕ) (x : HR (borelInv SK) lo) :
    HRmap (borelHom Φ) (lo + k) (innerPow SK lo k x) =
      innerPow SL lo k (HRmap (borelHom Φ) lo x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [innerPow_succ, innerPow_succ, ← ih]
    exact HRmap_innerStep Φ (lo + k) (innerPow SK lo k x)

end Algebra

variable {n : ℕ} (F : ReversibleMetric n)

/-- A power of the reflection class vanishing at the lower cut vanishes at the upper cut if
restriction is injective. -/
theorem nilpotent_of_injective {a b : ℝ} (hab : a ≤ b)
    (hinj : ∀ q, Function.Injective (HRmap (borelHom (cutComm F hab)) q)) {k : ℕ}
    (h : ∀ (lo : ℕ) (x : HK F a lo), innerPow (halfCommuting F a) lo k x = 0) (lo : ℕ)
    (x : HK F b lo) : innerPow (halfCommuting F b) lo k x = 0 := by
  apply hinj (lo + k)
  rw [HRmap_innerPow, h, map_zero]

/-- If the reflection class acts as zero on the K-Borel cohomology of the crossing pair, a k-th
power vanishing at the lower cut gives a (k+1)-st power vanishing at the upper cut. -/
theorem nilpotent_of_crossing {a b : ℝ} (hab : a ≤ b)
    (hw : ∀ (q : ℕ) (z : HKCross F hab q),
      BorelGraded.onHR (innerW (halfCommutingCross F hab)) q z = 0) {k : ℕ}
    (h : ∀ (lo : ℕ) (x : HK F a lo), innerPow (halfCommuting F a) lo k x = 0) (lo : ℕ)
    (x : HK F b lo) : innerPow (halfCommuting F b) lo (k + 1) x = 0 := by
  have hcut : HRmap (borelHom (cutComm F hab)) (lo + k)
      (innerPow (halfCommuting F b) lo k x) = 0 := by
    rw [HRmap_innerPow, h]
  obtain ⟨z, hz⟩ := Finsler.BorelCrossingK.exact_crossing F hab (lo + k) _ hcut
  rw [innerPow_succ, ← hz, ← HRmap_innerStep, innerStep_apply, hw, map_zero, map_zero]

/-- The K-Borel cohomology of (t_b, M) vanishes for all small b > 0. -/
theorem exists_HK_lev_eq_zero :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ → ∀ (q : ℕ) (x : HK F b q), x = 0 := by
  obtain ⟨b₀, hb₀, hzero⟩ := Finsler.SmallLevel.exists_HR_lev_eq_zero F
  exact ⟨b₀, hb₀, fun b hb hbb q x =>
    HR_borelInv_eq_zero (halfCommuting F b) (hzero b hb hbb) q x⟩

/-- With finitely many prime closed geodesic images, the reflection class is nilpotent on the
K-Borel cohomology of (t_a, M) at every regular cut a > 0. -/
theorem exists_innerW_nilpotent (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (a : ℝ)
    (ha : 0 < a) (hac : a ∉ crit F) :
    ∃ k : ℕ, ∀ (lo : ℕ) (x : HK F a lo), innerPow (halfCommuting F a) lo k x = 0 := by
  refine Finsler.NilpotentW.exists_of_levels F hfin
    (fun a k => ∀ (lo : ℕ) (x : HK F a lo), innerPow (halfCommuting F a) lo k x = 0)
    ?_ ?_ ?_ a ha hac
  · obtain ⟨b₀, hb₀, hzero⟩ := exists_HK_lev_eq_zero F
    exact ⟨b₀, hb₀, fun b hb hbb lo x => hzero b hb hbb lo x⟩
  · intro a b ha hab hreg k hk
    obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn a b b ha hab le_rfl hreg
    exact nilpotent_of_injective F hab
      (fun q => (Finsler.BorelDeformation.cut_bijective_K F hab (toDeformationConsts D) q).1) hk
  · intro a b ha hab hac hbc hsub k hk
    exact nilpotent_of_crossing F hab
      (fun q z => Finsler.CrossingWK.crossWK_zero_of_finite F hn hfin hab ha hac hbc hsub q z) hk

end

end Finsler.NilpotentWK
