module

public import Finsler.Topology.FixedAmbientSupport
public import Finsler.Topology.RestrictedRootSupport
public import Finsler.Topology.ProductRootSupport

/-! The actual half-fixed root lens inherits a prescribed loop crossing support cutoff.
Closedness, flow invariance and compact bands are supplied for the ambient penalized energy.
Strict descent and the two disjoint open root labels remain explicit hypotheses. -/

@[expose] public section

namespace Finsler.FixedRootLens

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.FlowLens Finsler.LensFamily
open Finsler.LensContinuation Finsler.AmbientPenalty Finsler.AmbientK
open Finsler.FixedAmbientNormalize Finsler.FixedAmbientSupport
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelFixed Finsler.FixedSampleK Finsler.CutPotential
open Finsler.ConeLens Finsler.ProductModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (M : ℕ) [NeZero M]

omit [NeZero M] in
theorem isClosed_fixOm : IsClosed (fixOm (n := n) M) :=
  isClosed_eq (ambK M).σ.continuous continuous_id

omit [NeZero M] in
theorem flow_fixed {g : Om n (2 * M) → ℝ} (D : Descent (TopCat.of (Om n (2 * M))) g)
    (hσ : ∀ t Q, D.flow t ((ambK M).σ Q) = (ambK M).σ (D.flow t Q)) :
    ∀ t (Q : Om n (2 * M)), 0 ≤ t → Q ∈ fixOm M → D.flow t Q ∈ fixOm M := by
  intro t Q _ hQ
  exact (hσ t Q).symm.trans (congrArg (D.flow t) hQ)

variable (F : ReversibleMetric n) (hn : 1 ≤ n) {lam l u c₀ : ℝ}

include hn in
theorem support_of_loop (hlam : 0 < lam) (hl : 0 < l) (hlu : l ≤ u)
    (D : Descent (TopCat.of (Om n (2 * M))) (penW F (2 * M) lam))
    (hσ : ∀ t Q, D.flow t ((ambK M).σ Q) = (ambK M).σ (D.flow t Q))
    (hlc : l ^ 2 < c₀) (hcu : c₀ < u ^ 2) {U R : Set (Om n (2 * M))}
    (hU : IsOpen U) (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) lam Q →
      penW F (2 * M) lam Q ≤ u ^ 2 → Q ∉ U ∪ R →
        penW F (2 * M) lam (D.flow 1 Q) < penW F (2 * M) lam Q)
    (hval : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) lam Q →
      penW F (2 * M) lam Q ≤ u ^ 2 → penW F (2 * M) lam Q ≠ c₀ →
        penW F (2 * M) lam (D.flow 1 Q) < penW F (2 * M) lam Q)
    (hsample : ∀ q, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := M) hl hlu)) q)) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hlu))) q))
    (hz : ∀ q, A ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hlu))) q, z = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b t : ℝ, 1 ≤ t → a < c₀ → c₀ < b → b - a < d →
      (∀ q, Module.Finite (ZMod 2)
        (lensH (Finsler.SubspaceK.subDescent D (flow_fixed M D hσ)) (Subtype.val ⁻¹' U) a b t q)) ∧
        ∀ q, A ≤ q → ∀ z :
          lensH (Finsler.SubspaceK.subDescent D (flow_fixed M D hσ)) (Subtype.val ⁻¹' U) a b t q,
          z = 0 := by
  obtain ⟨hfa, hza⟩ := ambient_support_of_loop M F hlam.le hl hlu hsample A hf hz
  exact Finsler.RestrictedRootSupport.support D (penW_continuous F hn lam)
    (isClosed_fixOm M) (flow_fixed M D hσ) hlc hcu (band_isCompact F hn hlam _ _)
    hU hR hUR hout hval (pow_le_pow_left₀ hl.le hlu 2) A hfa hza

include hn in
theorem product_support_of_loop (k : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hlam : 0 < lam) (hl : 0 < l) (hlu : l ≤ u)
    (D : Descent (TopCat.of (Om n (2 * M))) (penW F (2 * M) lam))
    (hσ : ∀ t Q, D.flow t ((ambK M).σ Q) = (ambK M).σ (D.flow t Q))
    (hlc : l ^ 2 < c₀) (hcu : c₀ < u ^ 2) {U R : Set (Om n (2 * M))}
    (hU : IsOpen U) (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) lam Q →
      penW F (2 * M) lam Q ≤ u ^ 2 → Q ∉ U ∪ R →
        penW F (2 * M) lam (D.flow 1 Q) < penW F (2 * M) lam Q)
    (hval : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) lam Q →
      penW F (2 * M) lam Q ≤ u ^ 2 → penW F (2 * M) lam Q ≠ c₀ →
        penW F (2 * M) lam (D.flow 1 Q) < penW F (2 * M) lam Q)
    (hsample : ∀ q, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := M) hl hlu)) q)) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hlu))) q))
    (hz : ∀ q, A ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hlu))) q, z = 0) :
    let ψ := Finsler.SubspaceK.subDescent D (flow_fixed M D hσ)
    let hh : Continuous (fun Q : TopCat.of (fixOm (n := n) M) => penW F (2 * M) lam Q) :=
      (penW_continuous F hn lam).comp continuous_subtype_val
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, 1 ≤ T → a < c₀ → c₀ < b →
      l ^ 2 ≤ a - (b - a) / (Real.exp (2 * T) - 1) →
      b + (b - a) / (Real.exp (2 * T) - 1) ≤ u ^ 2 →
      (b + (b - a) / (Real.exp (2 * T) - 1)) - (a - (b - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh)
          (over k V (Subtype.val ⁻¹' U)) a b T))) q)) ∧
        ∀ q, q < k ∨ k + A ≤ q → ∀ z :
          H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V ψ hh)
            (over k V (Subtype.val ⁻¹' U)) a b T))) q, z = 0 := by
  dsimp only
  obtain ⟨hfa, hza⟩ := ambient_support_of_loop M F hlam.le hl hlu hsample A hf hz
  obtain ⟨hfi, hzi⟩ := Finsler.SubspacePairs.support_inside (fixOm M)
    (sub_mono (penW F (2 * M) lam) (pow_le_pow_left₀ hl.le hlu 2)) A hfa hza
  have hKi : IsCompact {Q : TopCat.of (fixOm (n := n) M) |
      l ^ 2 ≤ penW F (2 * M) lam Q ∧ penW F (2 * M) lam Q ≤ u ^ 2} :=
    (isClosed_fixOm M).isClosedEmbedding_subtypeVal.isCompact_preimage (band_isCompact F hn hlam _ _)
  apply Finsler.ProductRootSupport.exists_support (Finsler.SubspaceK.subDescent D (flow_fixed M D hσ))
    ((penW_continuous F hn lam).comp continuous_subtype_val) k V hlc hcu hKi
    (hU.preimage continuous_subtype_val) (hR.preimage continuous_subtype_val) (hUR.preimage _) _ _
    (pow_le_pow_left₀ hl.le hlu 2) A hfi hzi
  · intro Q ha hb hQ
    change penW F (2 * M) lam (D.flow (max 1 0) Q) < penW F (2 * M) lam Q
    rw [max_eq_left zero_le_one]
    exact hout Q Q.2 ha hb hQ
  · intro Q ha hb hQ
    change penW F (2 * M) lam (D.flow (max 1 0) Q) < penW F (2 * M) lam Q
    rw [max_eq_left zero_le_one]
    exact hval Q Q.2 ha hb hQ

include hn in
theorem ambient_support_of_loop (hlam : 0 < lam) (hl : 0 < l) (hlu : l ≤ u)
    (D : Descent (TopCat.of (Om n (2 * M))) (penW F (2 * M) lam))
    (hσ : ∀ t Q, D.flow t ((ambK M).σ Q) = (ambK M).σ (D.flow t Q))
    (hlc : l ^ 2 < c₀) (hcu : c₀ < u ^ 2) {U R : Set (Om n (2 * M))}
    (hU : IsOpen U) (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) lam Q →
      penW F (2 * M) lam Q ≤ u ^ 2 → Q ∉ U ∪ R →
        penW F (2 * M) lam (D.flow 1 Q) < penW F (2 * M) lam Q)
    (hval : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) lam Q →
      penW F (2 * M) lam Q ≤ u ^ 2 → penW F (2 * M) lam Q ≠ c₀ →
        penW F (2 * M) lam (D.flow 1 Q) < penW F (2 * M) lam Q)
    (hsample : ∀ q, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := M) hl hlu)) q)) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hlu))) q))
    (hz : ∀ q, A ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hlu))) q, z = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b t : ℝ, 1 ≤ t → a < c₀ → c₀ < b → b - a < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (inter_subset_inter_left (fixOm M)
          (partY_sub_partU (penW F (2 * M) lam) D U a b t)))) q)) ∧
        ∀ q, A ≤ q → ∀ z :
          H (triv (pairOf (inter_subset_inter_left (fixOm M)
            (partY_sub_partU (penW F (2 * M) lam) D U a b t)))) q, z = 0 := by
  obtain ⟨d, hd, hs⟩ := support_of_loop M F hn hlam hl hlu D hσ hlc hcu hU hR hUR hout hval
    hsample A hf hz
  refine ⟨d, hd, fun a b t ht ha hb hw => ?_⟩
  obtain ⟨hfi, hzi⟩ := hs a b t ht ha hb hw
  exact Finsler.RestrictedLensPairs.support_outside D (flow_fixed M D hσ) U a b t
    (zero_le_one.trans ht) A hfi hzi

end

end Finsler.FixedRootLens
