module

public import Finsler.Topology.FiniteCut
public import Finsler.Topology.GysinCount
public import Finsler.Topology.Defect

/-! Dimension counts at regular finite cuts, for finitely many prime closed geodesic images.
The K-Borel cohomology of (t_a, M) has a stable dimension in high degrees, and the total
dimension of the reflection Borel cohomology of (t_a, M) is this stable dimension plus twice
the total dimension of the kernel of multiplication by v on the K-Borel cohomology (the
dimension count of the sign sequence of K over R). The total dimension of the ordinary
relative cohomology of (t_a, M) is twice the total dimension of the kernel of w on the
reflection Borel cohomology. The defect of the cut is a finite sum, and the defect plus the
total rank of the restriction of global classes is the total dimension of the reflection
Borel cohomology of (t_a, M). -/

@[expose] public section

namespace Finsler.CutCount

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelLoop Finsler.BorelCochain
open Finsler.CriticalLevels Finsler.BorelK Finsler.GysinCount Finsler.FiniteCut

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The dimension count of the sign sequence of K over R at a regular cut: the K-Borel
cohomology of (t_a, M) has a stable dimension in high degrees, and the total dimension of the
reflection Borel cohomology is this dimension plus twice the total dimension of the kernel of
v. -/
theorem exists_count_K (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ crit F) :
    ∃ Q₁ : ℕ, (∀ q, Q₁ ≤ q → ∀ x : HR (levComplex F a) q, x = 0) ∧
      (∀ q, Q₁ ≤ q → finrank (ZMod 2) (HK F a q) = finrank (ZMod 2) (HK F a Q₁)) ∧
      ∀ Q, Q₁ ≤ Q → ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (HR (levComplex F a) q) =
        finrank (ZMod 2) (HK F a Q) +
          2 * ∑ q ∈ Finset.range (Q + 1),
            finrank (ZMod 2) (LinearMap.ker (w (kComplex F a) q)) := by
  obtain ⟨Q₁, hfinR, hzeroR⟩ := exists_finite_HR F hn hfin ha hac
  have hH : ∀ q, Module.Finite (ZMod 2) (H (kComplex F a) q) := fun q => by
    have := hfinR q
    exact Module.Finite.equiv (forgetTargetEquiv F a q).symm
  have hR : ∀ q, Module.Finite (ZMod 2) (HR (kComplex F a) q) := fun q =>
    finite_HK F hn hfin ha hac q
  have hzero : ∀ q, Q₁ ≤ q → ∀ z : H (kComplex F a) q, z = 0 := fun q hq z => by
    apply (forgetTargetEquiv F a q).injective
    rw [hzeroR q hq (forgetTargetEquiv F a q z), map_zero]
  refine ⟨Q₁, hzeroR, fun q hq => finrank_HR_stable hzero q hq, fun Q hQ => ?_⟩
  have h := total_count hzero Q hQ
  rw [← h]
  exact Finset.sum_congr rfl fun q _ => (forgetTargetEquiv F a q).finrank_eq.symm

/-- The dimension count of the Gysin sequence of the reversal at a regular cut: the total
dimension of the ordinary relative cohomology of (t_a, M) is twice the total dimension of the
kernel of w on the reflection Borel cohomology. -/
theorem exists_count_R (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ crit F) :
    ∃ Q₁ : ℕ, ∀ Q, Q₁ ≤ Q →
      ∑ q ∈ Finset.range (Q + 1), finrank (ZMod 2) (H (levComplex F a) q) =
        2 * ∑ q ∈ Finset.range (Q + 1),
          finrank (ZMod 2) (LinearMap.ker (w (levComplex F a) q)) := by
  obtain ⟨k₁, hH, hzeroH⟩ := exists_finite_H F hn hfin ha hac
  obtain ⟨k₂, hR, hzeroR⟩ := exists_finite_HR F hn hfin ha hac
  refine ⟨max k₁ k₂, fun Q hQ => ?_⟩
  have h := total_count hzeroH Q ((le_max_left k₁ k₂).trans hQ)
  have hsub : Subsingleton (HR (levComplex F a) Q) :=
    ⟨fun x y => by
      rw [hzeroR Q ((le_max_right k₁ k₂).trans hQ) x,
        hzeroR Q ((le_max_right k₁ k₂).trans hQ) y]⟩
  have h0 : finrank (ZMod 2) (HR (levComplex F a) Q) = 0 := finrank_zero_of_subsingleton
  rw [h, h0, zero_add]

/-- The defect of a regular cut is a finite sum, and together with the total rank of the
restriction of global classes it is the total dimension of the reflection Borel cohomology of
(t_a, M). -/
theorem exists_defect_count (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ crit F) :
    ∃ Q₁ : ℕ, ∀ Q, Q₁ ≤ Q → Defect.defect F a +
        ∑ q ∈ Finset.range Q, finrank (ZMod 2) (LinearMap.range (HRmap (resHom F a) q)) =
      ∑ q ∈ Finset.range Q, finrank (ZMod 2) (HR (levComplex F a) q) := by
  obtain ⟨Q₁, hR, hzeroR⟩ := exists_finite_HR F hn hfin ha hac
  refine ⟨Q₁, fun Q hQ => ?_⟩
  have hsupp : (Function.support fun j : ℕ => finrank (ZMod 2) (Defect.coker F a j)) ⊆
      ↑(Finset.range Q) := by
    intro j hj
    rw [Finset.coe_range, mem_Iio]
    by_contra hjQ
    apply hj
    have hsub : Subsingleton (Defect.coker F a j) :=
      ⟨fun x y => by
        obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [hzeroR j (by omega) x', hzeroR j (by omega) y']⟩
    exact finrank_zero_of_subsingleton
  have hdef : Defect.defect F a =
      ∑ q ∈ Finset.range Q, finrank (ZMod 2) (Defect.coker F a q) :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hdef, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have := hR q
  exact Submodule.finrank_quotient_add_finrank (LinearMap.range (HRmap (resHom F a) q))

end

end Finsler.CutCount
