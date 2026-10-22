module

public import Finsler.Topology.TorsionK
public import Finsler.Topology.DoublingDefect
public import Finsler.Algebra.PartnerRank

/-! The doubling rank budget at a regular cut, from two rank statements about global classes. At
a regular cut 2a, with finitely many prime closed geodesic images, let E be the restrictions to
(t_{2a}, M) of the global K-classes, t the total dimension of the kernel of v on the K-Borel
cohomology of (t_{2a}, M), and V(c) the total rank of the restriction of global reflection
classes to the cut c. Then

  T(2a) − T(a) = 2t − V(2a) + V(a),   dim fgt(E) ≤ V(a) + t,   dim fgt(E_k) ≤ t,

where E_k ⊆ E are the restrictions of the global K-classes annihilated by the k-th power of
U = v(v + w). Suppose given labels with numbers b_i and p_i ≤ b_i such that

* Σ b_i ≤ dim fgt(E_k) for some k, and
* V(2a) ≤ dim fgt(E) + Σ p_i.

Then the numbers T(a), T(2a), J = t − Σ b_i, V_e = V(2a) − Σ (b_i + p_i), V = V(a) satisfy the
rank identity and the inequalities of the doubling formula (`PartnerRank.Data`). In the intended
use the labels are the bottom classes of the odd stages, b_i is one when the class is nonzero on
t_{2a}, and p_i is one when its evaluation-cup partner is independent of the bottom classes
there: bottom classes of odd stages are forgetful images of global K-classes annihilated by a
power of U, and every other class of the global basis is the forgetful image of a global
K-class. The two hypotheses are statements about the global basis and are not proved. -/

@[expose] public section

namespace Finsler.DoublingBudget

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelLoop Finsler.BorelCochain
open Finsler.CriticalLevels Finsler.BorelIterate Finsler.BorelK Finsler.FiniteCut
open Finsler.VisibleBound Finsler.DoublingDefect Finsler.TorsionK

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The doubling rank budget at a regular cut 2a from the two rank statements about global
classes described above. -/
theorem exists_budget (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q₀ : ℕ, ∀ D, Q₀ ≤ D → ∀ {ι : Type} (labels : Finset ι) (b p : ι → ℤ) (k : ℕ),
      (∀ i ∈ labels, p i ≤ b i) →
      ∑ i ∈ labels, b i ≤ ((∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
        (((annSub (halfCommutingFull n) k q).map
          (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) : ℕ) : ℤ) →
      ((∑ q ∈ Finset.range (D + 1),
        finrank (ZMod 2) (LinearMap.range (HRmap (resHom F (2 * a)) q)) : ℕ) : ℤ) ≤
        ((∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
          ((LinearMap.range (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) : ℕ) : ℤ) + ∑ i ∈ labels, p i →
      ∃ s : Finsler.PartnerRank.Data ι, s.labels = labels ∧ s.bottom = b ∧ s.partner = p ∧
        s.T = (Defect.defect F a : ℤ) ∧ s.Tdouble = (Defect.defect F (2 * a) : ℤ) := by
  obtain ⟨Q₁, hdd⟩ := exists_defect_double F hn hfin ha h2a
  obtain ⟨Q₂, hvb⟩ := exists_visible_bound F hn hfin ha h2a
  obtain ⟨Q₃, htc⟩ := exists_torsion_count F hn hfin ha h2a
  refine ⟨Q₁ + Q₂ + Q₃, fun D hD ι labels b p k hpb hN hV => ?_⟩
  have e1 := hdd (D + 1) (by omega)
  have e2 := hvb D (by omega)
  have e3 := htc D (by omega) k
  have e4 : ∑ i ∈ labels, (b i + p i) = ∑ i ∈ labels, b i + ∑ i ∈ labels, p i :=
    Finset.sum_add_distrib
  have e5 : ∑ q ∈ Finset.range D,
        finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) ≤
      ∑ q ∈ Finset.range (D + 1),
        finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) := by
    rw [Finset.sum_range_succ]
    exact Nat.le_add_right _ _
  refine ⟨{ labels := labels
            bottom := b
            partner := p
            T := (Defect.defect F a : ℤ)
            Tdouble := (Defect.defect F (2 * a) : ℤ)
            J := ((∑ q ∈ Finset.range (D + 1),
              finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) : ℕ) : ℤ) -
                ∑ i ∈ labels, b i
            Ve := ((∑ q ∈ Finset.range (D + 1),
              finrank (ZMod 2) (LinearMap.range (HRmap (resHom F (2 * a)) q)) : ℕ) : ℤ) -
                ∑ i ∈ labels, (b i + p i)
            V := ((∑ q ∈ Finset.range (D + 1),
              finrank (ZMod 2) (LinearMap.range (HRmap (resHom F a) q)) : ℕ) : ℤ)
            rank := ?_
            fixed := ?_
            nonnegJ := ?_
            partner_le := hpb }, rfl, rfl, rfl, rfl, rfl⟩
  · omega
  · omega
  · omega

/-- Under the two rank statements about global classes, the defect does not decrease from a to
2a, and if it stays the same every partner number equals its bottom number. -/
theorem exists_defect_le_double (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : 0 < a) (h2a : 2 * a ∉ crit F) :
    ∃ Q₀ : ℕ, ∀ D, Q₀ ≤ D → ∀ {ι : Type} (labels : Finset ι) (b p : ι → ℤ) (k : ℕ),
      (∀ i ∈ labels, p i ≤ b i) →
      ∑ i ∈ labels, b i ≤ ((∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
        (((annSub (halfCommutingFull n) k q).map
          (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) : ℕ) : ℤ) →
      ((∑ q ∈ Finset.range (D + 1),
        finrank (ZMod 2) (LinearMap.range (HRmap (resHom F (2 * a)) q)) : ℕ) : ℤ) ≤
        ((∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
          ((LinearMap.range (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) : ℕ) : ℤ) + ∑ i ∈ labels, p i →
      Defect.defect F a ≤ Defect.defect F (2 * a) ∧
        (Defect.defect F (2 * a) = Defect.defect F a → ∀ i ∈ labels, p i = b i) := by
  obtain ⟨Q₀, h⟩ := exists_budget F hn hfin ha h2a
  refine ⟨Q₀, fun D hD ι labels b p k hpb hN hV => ?_⟩
  obtain ⟨s, hl, hb, hp, hT1, hT2⟩ := h D hD labels b p k hpb hN hV
  have hmono := Finsler.PartnerRank.doubling_monotone s
  rw [hT1, hT2] at hmono
  refine ⟨by exact_mod_cast hmono, fun heq i hi => ?_⟩
  have heq' : s.Tdouble = s.T := by
    rw [hT1, hT2, heq]
  have h1 := Finsler.PartnerRank.equality_forces_partner s heq' i (by rw [hl]; exact hi)
  rw [hb, hp] at h1
  exact h1

end

end Finsler.DoublingBudget
