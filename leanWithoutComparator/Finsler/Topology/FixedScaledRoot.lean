module

public import Finsler.Topology.FixedRootLens
public import Finsler.Topology.ScaledRootSupport

/-! The actual fixed root energy m² pen(1/m) and its unchanged root ODE. -/

@[expose] public section

namespace Finsler.FixedScaledRoot

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.FlowLens Finsler.LensFamily
open Finsler.AmbientPenalty Finsler.AmbientK Finsler.FixedAmbientNormalize
open Finsler.FixedAmbientSupport Finsler.FixedRootLens Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.BorelFixed Finsler.FixedSampleK Finsler.CutPotential
open Finsler.ConeLens Finsler.ProductModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (M : ℕ) [NeZero M] (F : ReversibleMetric n) (hn : 1 ≤ n) {l u c₀ : ℝ}

include hn in
theorem product_support (m : ℕ) [NeZero m] (k : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hl : 0 < l) (hlu : l ≤ u)
    (D : Descent (TopCat.of (Om n (2 * M))) (penW F (2 * M) (1 / (m : ℝ))))
    (hσ : ∀ t Q, D.flow t ((ambK M).σ Q) = (ambK M).σ (D.flow t Q))
    (hlc : l ^ 2 < c₀) (hcu : c₀ < u ^ 2) {U R : Set (Om n (2 * M))}
    (hU : IsOpen U) (hR : IsOpen R) (hUR : Disjoint U R)
    (hout : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) (1 / (m : ℝ)) Q →
      penW F (2 * M) (1 / (m : ℝ)) Q ≤ u ^ 2 → Q ∉ U ∪ R →
        penW F (2 * M) (1 / (m : ℝ)) (D.flow 1 Q) < penW F (2 * M) (1 / (m : ℝ)) Q)
    (hval : ∀ Q ∈ fixOm M, l ^ 2 ≤ penW F (2 * M) (1 / (m : ℝ)) Q →
      penW F (2 * M) (1 / (m : ℝ)) Q ≤ u ^ 2 → penW F (2 * M) (1 / (m : ℝ)) Q ≠ c₀ →
        penW F (2 * M) (1 / (m : ℝ)) (D.flow 1 Q) < penW F (2 * M) (1 / (m : ℝ)) Q)
    (hsample : ∀ q, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := M) hl hlu)) q)) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hlu))) q))
    (hz : ∀ q, A ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hlu))) q, z = 0) :
    let ψ := Finsler.SubspaceK.subDescent D (flow_fixed M D hσ)
    let hh : Continuous (fun Q : TopCat.of (fixOm (n := n) M) =>
      (m : ℝ) ^ 2 * penW F (2 * M) (1 / (m : ℝ)) Q) :=
      continuous_const.mul ((penW_continuous F hn (1 / (m : ℝ))).comp continuous_subtype_val)
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, 1 ≤ T → a < (m : ℝ) ^ 2 * c₀ → (m : ℝ) ^ 2 * c₀ < b →
      (m : ℝ) ^ 2 * l ^ 2 ≤ a - (b - a) / (Real.exp (2 * T) - 1) →
      b + (b - a) / (Real.exp (2 * T) - 1) ≤ (m : ℝ) ^ 2 * u ^ 2 →
      (b + (b - a) / (Real.exp (2 * T) - 1)) - (a - (b - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V (Finsler.ScaledRootSupport.scaleDescent ψ ((m : ℝ) ^ 2) (sq_nonneg _)) hh)
          (over k V (Subtype.val ⁻¹' U)) a b T))) q)) ∧
        ∀ q, q < k ∨ k + A ≤ q → ∀ z :
          H (triv (pairOf (setY_sub_setU (cone k V hh) (descent k V (Finsler.ScaledRootSupport.scaleDescent ψ ((m : ℝ) ^ 2) (sq_nonneg _)) hh)
            (over k V (Subtype.val ⁻¹' U)) a b T))) q, z = 0 := by
  dsimp only
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hlam : (0 : ℝ) < 1 / (m : ℝ) := div_pos zero_lt_one hm
  obtain ⟨hfa, hza⟩ := ambient_support_of_loop M F hlam.le hl hlu hsample A hf hz
  obtain ⟨hfi, hzi⟩ := Finsler.SubspacePairs.support_inside (fixOm M)
    (sub_mono (penW F (2 * M) (1 / (m : ℝ))) (pow_le_pow_left₀ hl.le hlu 2)) A hfa hza
  have hKi : IsCompact {Q : TopCat.of (fixOm (n := n) M) |
      l ^ 2 ≤ penW F (2 * M) (1 / (m : ℝ)) Q ∧ penW F (2 * M) (1 / (m : ℝ)) Q ≤ u ^ 2} :=
    (isClosed_fixOm M).isClosedEmbedding_subtypeVal.isCompact_preimage (band_isCompact F hn hlam _ _)
  apply Finsler.ScaledRootSupport.product_support (Finsler.SubspaceK.subDescent D (flow_fixed M D hσ))
    ((penW_continuous F hn (1 / (m : ℝ))).comp continuous_subtype_val) ((m : ℝ) ^ 2)
    (sq_pos_of_pos hm) k V hlc hcu hKi
    (hU.preimage continuous_subtype_val) (hR.preimage continuous_subtype_val) (hUR.preimage _) _ _
    (pow_le_pow_left₀ hl.le hlu 2) A hfi hzi
  · intro Q ha hb hQ
    change penW F (2 * M) (1 / (m : ℝ)) (D.flow (max 1 0) Q) < penW F (2 * M) (1 / (m : ℝ)) Q
    rw [max_eq_left zero_le_one]
    exact hout Q Q.2 ha hb hQ
  · intro Q ha hb hQ
    change penW F (2 * M) (1 / (m : ℝ)) (D.flow (max 1 0) Q) < penW F (2 * M) (1 / (m : ℝ)) Q
    rw [max_eq_left zero_le_one]
    exact hval Q Q.2 ha hb hQ

end

end Finsler.FixedScaledRoot

