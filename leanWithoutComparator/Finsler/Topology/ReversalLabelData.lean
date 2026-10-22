module

public import Finsler.Topology.AmbientK
public import Finsler.Analysis.InvolutionConjugacy
public import Finsler.Topology.LensConjugacy

/-! analytic label data and lens ranks transported by reversal.
 Actual oriented-family assembly remains separate. -/

@[expose] public section

namespace Finsler.ReversalLabelData

open Set Topology CategoryTheory Finsler.SphereGeometry Finsler.Geometry
open Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.PolygonDescentK
open Finsler.RevLabel Finsler.AmbientK Finsler.EquivariantField Finsler.InvolutionConjugacy
open Finsler.FlowLens Finsler.LensContinuation Finsler.BorelPair Finsler.BorelLoop
open Finsler.AmbientDescent
open Finsler.BorelCochain Finsler.PairTriple
open scoped ContDiff NNReal
noncomputable section

variable {n : ℕ} (M : ℕ) [NeZero M]

def reversalHomeo : Om n (2 * M) ≃ₜ Om n (2 * M) where
  toFun := (ambK M).ρ
  invFun := (ambK M).ρ
  left_inv := (ambK M).ρρ
  right_inv := (ambK M).ρρ
  continuous_toFun := (ambK M).ρ.continuous
  continuous_invFun := (ambK M).ρ.continuous

theorem deform_rev (F : ReversibleMetric n) (lam : ℝ)
    (β : (ZMod (2 * M) → Ambient n) → ℝ) (Q : ZMod (2 * M) → Ambient n) :
    pen F (2 * M) lam (revA (2 * M) Q) + β (revA (2 * M) (revA (2 * M) Q)) =
      pen F (2 * M) lam Q + β Q := by
  rw [pen_revA, revA_revA]

theorem deformed_derivative (F : ReversibleMetric n) (lam : ℝ)
    (β : (ZMod (2 * M) → Ambient n) → ℝ)
    (W : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n)
    {Q : ZMod (2 * M) → Ambient n}
    (hd : DifferentiableAt ℝ (fun y => pen F (2 * M) lam y + β y) (revA (2 * M) Q)) :
    fderiv ℝ (fun y => pen F (2 * M) lam y + β (revA (2 * M) y)) Q (revField W Q) =
      fderiv ℝ (fun y => pen F (2 * M) lam y + β y) (revA (2 * M) Q) (W (revA (2 * M) Q)) := by
  have he : conjFun (revA (2 * M)) (fun y => pen F (2 * M) lam y + β y) =
      (fun y => pen F (2 * M) lam y + β (revA (2 * M) y)) := by
    funext y
    change pen F (2 * M) lam (revA (2 * M) y) + _ = _
    rw [pen_revA]
  have h := conj_derivative (revA (2 * M)) (revA_revA (2 * M)) hd W
  rwa [he] at h

theorem reverse_analytic (F : ReversibleMetric n)
    {U C T : Set (ZMod (2 * M) → Ambient n)}
    {W : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n}
    {β : (ZMod (2 * M) → Ambient n) → ℝ} {η : ℝ}
    (hU : IsOpen U) (hUr : U ⊆ Finsler.LevelField.regSet F (2 * M) 1)
    (hW : ContDiffOn ℝ ∞ W U)
    (hle : ∀ y ∈ U, fderiv ℝ (pen F (2 * M) 1) y (W y) ≤ 0)
    (hlt : ∀ y ∈ U, y ∉ C → fderiv ℝ (pen F (2 * M) 1) y (W y) < 0)
    (hT : IsCompact T) (hTU : T ⊆ U) (hβT : tsupport β ⊆ T)
    (hβd : ∀ y, DifferentiableAt ℝ β y) (hβb : ∀ y, |β y| ≤ η)
    (hβle : ∀ y ∈ tsupport β, fderiv ℝ (fun y => pen F (2 * M) 1 y + β y) y (W y) ≤ 0)
    (hβlt : ∀ y ∈ tsupport β, y ∉ C →
      fderiv ℝ (fun y => pen F (2 * M) 1 y + β y) y (W y) < 0) :
    IsOpen (revA (2 * M) ⁻¹' U) ∧
    revA (2 * M) ⁻¹' U ⊆ Finsler.LevelField.regSet F (2 * M) 1 ∧
    ContDiffOn ℝ ∞ (revField W) (revA (2 * M) ⁻¹' U) ∧
    (∀ y ∈ revA (2 * M) ⁻¹' U, fderiv ℝ (pen F (2 * M) 1) y (revField W y) ≤ 0) ∧
    (∀ y ∈ revA (2 * M) ⁻¹' U, y ∉ revA (2 * M) ⁻¹' C →
      fderiv ℝ (pen F (2 * M) 1) y (revField W y) < 0) ∧
    IsCompact (revA (2 * M) ⁻¹' T) ∧
    revA (2 * M) ⁻¹' T ⊆ revA (2 * M) ⁻¹' U ∧
    tsupport (conjFun (revA (2 * M)) β) ⊆ revA (2 * M) ⁻¹' T ∧
    (∀ y, DifferentiableAt ℝ (conjFun (revA (2 * M)) β) y) ∧
    (∀ y, |conjFun (revA (2 * M)) β y| ≤ η) ∧
    (∀ y ∈ tsupport (conjFun (revA (2 * M)) β),
      fderiv ℝ (fun y => pen F (2 * M) 1 y + β (revA (2 * M) y)) y (revField W y) ≤ 0) ∧
    (∀ y ∈ tsupport (conjFun (revA (2 * M)) β), y ∉ revA (2 * M) ⁻¹' C →
      fderiv ℝ (fun y => pen F (2 * M) 1 y + β (revA (2 * M) y)) y (revField W y) < 0) := by
  let r := revA (n := n) (2 * M)
  have hr : ∀ y, r (r y) = y := revA_revA (2 * M)
  have hs : ∀ y, y ∈ tsupport (conjFun r β) → r y ∈ tsupport β := by
    intro y hy
    rw [tsupport_conjFun r hr] at hy
    exact hy
  have hd : ∀ y, y ∈ tsupport (conjFun r β) →
      DifferentiableAt ℝ (fun y => pen F (2 * M) 1 y + β y) (r y) :=
    fun y hy => ((hUr (hTU (hβT (hs y hy)))).2.differentiableAt one_ne_zero).add (hβd _)
  refine ⟨hU.preimage r.continuous, ?_, conjField_contDiffOn r hW, ?_, ?_,
    (invHomeo r hr).isCompact_preimage.mpr hT, fun _ hy => hTU hy, ?_, ?_, (fun y => hβb (r y)), ?_, ?_⟩
  · intro y hy
    have h := regSet_revA F 1 (hUr hy)
    rwa [hr] at h
  · intro y hy
    rw [show revField W y = r (W (r y)) from rfl,
      fderiv_inv r hr (fun x => pen_revA F 1 x) ((hUr hy).2.differentiableAt one_ne_zero)]
    exact hle _ hy
  · intro y hy hC
    rw [show revField W y = r (W (r y)) from rfl,
      fderiv_inv r hr (fun x => pen_revA F 1 x) ((hUr hy).2.differentiableAt one_ne_zero)]
    exact hlt _ hy hC
  · exact fun y hy => hβT (hs y hy)
  · exact fun y => (hβd (r y)).comp y r.differentiableAt
  · intro y hy
    rw [deformed_derivative M F 1 β W (hd y hy)]
    exact hβle _ (hs y hy)
  · intro y hy hC
    rw [deformed_derivative M F 1 β W (hd y hy)]
    exact hβlt _ (hs y hy) hC

theorem reverse_half_field
    {U : Set (ZMod (2 * M) → Ambient n)}
    {W : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n}
    (hW : ∀ y ∈ U, W (rotA (2 * M) (M : ZMod (2 * M)) y) =
      rotA (2 * M) (M : ZMod (2 * M)) (W y))
    {Q : ZMod (2 * M) → Ambient n} (hQ : Q ∈ revA (2 * M) ⁻¹' U) :
    revField W (rotA (2 * M) (M : ZMod (2 * M)) Q) =
      rotA (2 * M) (M : ZMod (2 * M)) (revField W Q) :=
  conjField_equivariant (revA (2 * M)) (rotA (2 * M) (M : ZMod (2 * M)))
    (revA_rotA (Finsler.SampleK.half_shift M)) hW hQ

omit [NeZero M] in
theorem reversal_lens_finrank {f g : Om n (2 * M) → ℝ}
    (D : Descent (Om n (2 * M)) f) (E : Descent (Om n (2 * M)) g)
    (hfun : ∀ Q, g ((ambK M).ρ Q) = f Q)
    (hflow : ∀ t Q, E.flow t ((ambK M).ρ Q) = (ambK M).ρ (D.flow t Q))
    (U : Set (Om n (2 * M))) (a b T : ℝ) (q : ℕ) :
    Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU f D U a b T))) q) =
      Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU g E ((ambK M).ρ ⁻¹' U) a b T))) q) := by
  exact Finsler.LensConjugacy.finrank_eq D E (reversalHomeo M) hfun hflow
    (fun Q => by change Q ∈ U ↔ (ambK M).ρ ((ambK M).ρ Q) ∈ U; rw [(ambK M).ρρ]) a b T q

/-- For actual ambient descents, the required flow conjugacy follows from ODE uniqueness. -/
theorem reversal_descent_lens_finrank
    {V : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n} {KL : ℝ≥0}
    (hL : LipschitzWith KL V)
    (hV0 : ∀ P : ZMod (2 * M) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
    {f g : (ZMod (2 * M) → Ambient n) → ℝ}
    {O O' : Set (ZMod (2 * M) → Ambient n)}
    (hf : ∀ P ∈ O, DifferentiableAt ℝ f P) (hs : ∀ P, V P ≠ 0 → P ∈ O)
    (hle : ∀ P ∈ O, fderiv ℝ f P (V P) ≤ 0)
    (hg : ∀ P ∈ O', DifferentiableAt ℝ g P)
    (hs' : ∀ P, revField V P ≠ 0 → P ∈ O')
    (hle' : ∀ P ∈ O', fderiv ℝ g P (revField V P) ≤ 0)
    (hfg : ∀ P, g (revA (2 * M) P) = f P)
    (U : Set (Om n (2 * M))) (a b T : ℝ) (q : ℕ) :
    Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU (fun Q : Om n (2 * M) => f Q.1)
      (descentOf hL hV0 hf hs hle) U a b T))) q) =
      Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU (fun Q : Om n (2 * M) => g Q.1)
        (descentOf (lipschitz_revField hL) (revField_ne_zero hV0) hg hs' hle')
        ((ambK M).ρ ⁻¹' U) a b T))) q) := by
  apply reversal_lens_finrank M
  · intro Q
    exact hfg Q.1
  · intro t Q
    exact flowOm_revField hL hV0 t Q

end

end Finsler.ReversalLabelData
