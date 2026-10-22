module

public import Finsler.Analysis.FormSemicontinuity
public import Finsler.Analysis.InvariantFrames
public import Finsler.Algebra.SymmetricBlocks
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Invariant nondegenerate bilinear forms restrict nondegenerately to involution eigenspaces.
Their indices are constant in continuous families; commuting holonomy gives closed frames. -/

@[expose] public section

namespace Finsler.InvolutionIndex

open Module QuadraticForm QuadraticMap

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Restriction to an eigenspace, using Mathlib's eigenspace submodule. -/
def eigenForm (T : Module.End ℝ V) (e : ℝ) (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    T.eigenspace e →ₗ[ℝ] T.eigenspace e →ₗ[ℝ] ℝ :=
  β.compl₁₂ (T.eigenspace e).subtype (T.eigenspace e).subtype

/-- The existing fixed-space model is the positive eigenspace. -/
theorem fixed_eq_eigenspace (T : Module.End ℝ V) :
    Finsler.SymmetricBlocks.fixed T = T.eigenspace 1 := by
  ext v
  rw [Finsler.SymmetricBlocks.mem_fixed, Module.End.mem_eigenspace_iff, one_smul]

/-- The existing two-term orbit-sum kernel is the negative eigenspace. -/
theorem normal_two_eq_eigenspace (T : Module.End ℝ V) :
    Finsler.SymmetricBlocks.normal T 2 = T.eigenspace (-1) := by
  ext v
  rw [Finsler.SymmetricBlocks.mem_normal, Module.End.mem_eigenspace_iff, neg_one_smul]
  have hp : Finsler.SymmetricBlocks.powSum T 2 v = v + T v := by
    simp [Finsler.SymmetricBlocks.powSum_apply, Finset.sum_range_succ]
  rw [hp]
  constructor
  · intro h
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  · intro h
    rw [h, add_neg_cancel]

/-- The two eigenspaces are orthogonal for an invariant bilinear form. -/
theorem eigenspaces_orthogonal (T : Module.End ℝ V) (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hinv : ∀ v w, β (T v) (T w) = β v w)
    (v : T.eigenspace 1) (w : T.eigenspace (-1)) : β (v : V) (w : V) = 0 := by
  have h := hinv v w
  rw [Module.End.mem_eigenspace_iff.mp v.2, Module.End.mem_eigenspace_iff.mp w.2,
    one_smul, neg_one_smul, map_neg] at h
  linarith

/-- The projector witness v + e T(v) detects every covector on the e-eigenspace. -/
theorem ker_eigenForm_eq_bot (T : Module.End ℝ V) (hTT : ∀ v, T (T v) = v)
    (e : ℝ) (he : e * e = 1) (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hinv : ∀ v w, β (T v) (T w) = β v w) (hker : LinearMap.ker β = ⊥) :
    LinearMap.ker (eigenForm T e β) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  have hxT : T (x : V) = e • (x : V) := Module.End.mem_eigenspace_iff.mp x.2
  have hxzero : β (x : V) = 0 := by
    apply LinearMap.ext
    intro v
    have hmem : v + e • T v ∈ T.eigenspace e := by
      rw [Module.End.mem_eigenspace_iff, map_add, map_smul, hTT,
        smul_add, smul_smul, he, one_smul]
      module
    have h1 := congrArg (fun φ : T.eigenspace e →ₗ[ℝ] ℝ => φ ⟨v + e • T v, hmem⟩)
      (LinearMap.mem_ker.mp hx)
    change β (x : V) (v + e • T v) = 0 at h1
    rw [map_add, map_smul, smul_eq_mul] at h1
    have h2 := hinv (x : V) v
    rw [hxT, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    change β (x : V) v = 0
    linarith
  have hxker : (x : V) ∈ LinearMap.ker β := LinearMap.mem_ker.mpr hxzero
  rw [hker, Submodule.mem_bot] at hxker
  exact Subtype.ext hxker

variable [FiniteDimensional ℝ V]

/-- The existing cyclic-block index theorem gives the sum of the two eigenspace indices. -/
theorem sigNeg_eq_eigenspace_add (T : Module.End ℝ V) (hTT : ∀ v, T (T v) = v)
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ v w, β v w = β w v)
    (hinv : ∀ v w, β (T v) (T w) = β v w) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap β) =
      sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T 1 β)) +
        sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T (-1) β)) := by
  have hp : T ^ 2 = 1 := by
    ext v
    change T (T v) = v
    exact hTT v
  have h := Finsler.SymmetricBlocks.sigNeg_eq_add (ρ := T) (k := 2) (β := β)
    (by norm_num) hp hsym hinv
  rw [fixed_eq_eigenspace, normal_two_eq_eigenspace] at h
  exact h

/-- The negative index on each involution eigenspace is constant in a continuous nondegenerate
invariant family over a preconnected parameter space. -/
theorem sigNeg_eigenForm_eq {Θ : Type*} [TopologicalSpace Θ] [PreconnectedSpace Θ]
    (T : Module.End ℝ V) (hTT : ∀ v, T (T v) = v) (e : ℝ) (he : e * e = 1)
    {B : Θ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hB : Continuous fun p : Θ × V × V => B p.1 p.2.1 p.2.2)
    (hsym : ∀ θ v w, B θ v w = B θ w v)
    (hinv : ∀ θ v w, B θ (T v) (T w) = B θ v w)
    (hker : ∀ θ, LinearMap.ker (B θ) = ⊥) (θ θ' : Θ) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T e (B θ))) =
      sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T e (B θ'))) := by
  have hc : Continuous fun p : Θ × T.eigenspace e × T.eigenspace e =>
      eigenForm T e (B p.1) p.2.1 p.2.2 := by
    exact hB.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
  apply Finsler.FormSemicontinuity.sigNeg_eq_of_finrank_ker_eq
    (B := fun θ => eigenForm T e (B θ)) hc
    (fun θ v w => hsym θ (v : V) (w : V)) ?_ θ θ'
  intro a a'
  rw [ker_eigenForm_eq_bot T hTT e he (B a) (hinv a) (hker a),
    ker_eigenForm_eq_bot T hTT e he (B a') (hinv a') (hker a')]

/-- The restricted family has the constant index required by the existing frame-path API. -/
theorem family_eigenForm (T : Module.End ℝ V) (hTT : ∀ v, T (T v) = v)
    (e : ℝ) (he : e * e = 1) {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hB : Continuous fun p : ℝ × V × V => B p.1 p.2.1 p.2.2)
    (hsym : ∀ θ v w, B θ v w = B θ w v)
    (hinv : ∀ θ v w, B θ (T v) (T w) = B θ v w)
    (hker : ∀ θ, LinearMap.ker (B θ) = ⊥) :
    Finsler.FramePath.Family (fun θ => eigenForm T e (B θ))
      (sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T e (B 0)))) := by
  apply Finsler.FrameIndex.family_of_sigNeg
  · exact hB.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
  · intro θ v w
    exact hsym θ v w
  · intro θ
    exact sigNeg_eigenForm_eq T hTT e he hB hsym hinv hker θ 0

/-- A commuting continuous linear map restricts to each eigenspace. -/
def onEigen (T : Module.End ℝ V) (e : ℝ) (R : V →L[ℝ] V)
    (hcomm : ∀ v, T (R v) = R (T v)) : T.eigenspace e →L[ℝ] T.eigenspace e :=
  (R.comp (T.eigenspace e).subtypeL).codRestrict (T.eigenspace e) fun x => by
    rw [Module.End.mem_eigenspace_iff]
    change T (R (x : V)) = e • R (x : V)
    rw [hcomm, Module.End.mem_eigenspace_iff.mp x.2, map_smul]

omit [FiniteDimensional ℝ V] in
theorem onEigen_coe (T : Module.End ℝ V) (e : ℝ) (R : V →L[ℝ] V)
    (hcomm : ∀ v, T (R v) = R (T v)) (x : T.eigenspace e) :
    (onEigen T e R hcomm x : V) = R (x : V) := rfl

omit [FiniteDimensional ℝ V] in
theorem onEigen_pow_coe (T : Module.End ℝ V) (e : ℝ) (R : V →L[ℝ] V)
    (hcomm : ∀ v, T (R v) = R (T v)) (j : ℕ) (x : T.eigenspace e) :
    (((onEigen T e R hcomm) ^ j) x : V) = (R ^ j) (x : V) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, pow_succ]
    change (((onEigen T e R hcomm) ^ j) (onEigen T e R hcomm x) : V) =
      (R ^ j) (R (x : V))
    rw [ih, onEigen_coe]

/-- **Closed frames inside involution eigenspaces.** The existing no-real-eigenvalue holonomy
criterion restricts to the eigenspaces of a commuting involution. This supplies the abstract
closed-frame construction for the pointwise fixed critical-circle case. -/
theorem exists_eigen_closed_frame (T : Module.End ℝ V) (hTT : ∀ v, T (T v) = v)
    (e : ℝ) (he : e * e = 1) {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hB : Continuous fun p : ℝ × V × V => B p.1 p.2.1 p.2.2)
    (hsym : ∀ θ v w, B θ v w = B θ w v)
    (hinv : ∀ θ v w, B θ (T v) (T w) = B θ v w)
    (hker : ∀ θ, LinearMap.ker (B θ) = ⊥)
    (R : V →L[ℝ] V) (hcomm : ∀ v, T (R v) = R (T v))
    {η : ℝ} (hη : 0 < η) (hR : ∀ θ v w, B (θ + η) (R v) (R w) = B θ v w)
    {r : ℕ} (hr : 0 < r)
    (hper : ∀ v w, B 0 ((R ^ (2 * r)) v) ((R ^ (2 * r)) w) = B 0 v w)
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hgs : ∀ v w, g v w = g w v)
    (hgp : ∀ v, v ≠ 0 → 0 < g v v)
    (hgR : ∀ v w, g ((R ^ (2 * r)) v) ((R ^ (2 * r)) w) = g v w)
    (heig : ∀ (μ : ℝ) (v : V), (R ^ (2 * r)) v = μ • v → v = 0) :
    ∃ H : ℝ → Fin (sigNeg (LinearMap.BilinMap.toQuadraticMap (eigenForm T e (B 0)))) →
        T.eigenspace e, Continuous H ∧ H (((2 * r : ℕ) : ℝ) * η) = H 0 ∧
      ∀ θ ∈ Set.Icc 0 (((2 * r : ℕ) : ℝ) * η),
        Finsler.DefiniteFrames.Neg (eigenForm T e (B θ)) (H θ) := by
  refine Finsler.InvariantFrames.exists_closed_frame_of_invariant
    (family_eigenForm T hTT e he hB hsym hinv hker) rfl (onEigen T e R hcomm) hη
    ?_ hr ?_ (eigenForm T e g) ?_ ?_ ?_ ?_
  · intro θ v w
    exact hR θ v w
  · intro v w
    change B 0 ((((onEigen T e R hcomm) ^ (2 * r)) v) : V)
      ((((onEigen T e R hcomm) ^ (2 * r)) w) : V) = B 0 (v : V) (w : V)
    rw [onEigen_pow_coe, onEigen_pow_coe]
    exact hper v w
  · intro v w
    exact hgs v w
  · intro v hv
    exact hgp v (fun hz => hv (Subtype.ext hz))
  · intro v w
    change g ((((onEigen T e R hcomm) ^ (2 * r)) v) : V)
      ((((onEigen T e R hcomm) ^ (2 * r)) w) : V) = g (v : V) (w : V)
    rw [onEigen_pow_coe, onEigen_pow_coe]
    exact hgR v w
  · intro μ v hv
    have h := congrArg Subtype.val hv
    rw [onEigen_pow_coe] at h
    exact Subtype.ext (heig μ v h)

end

end Finsler.InvolutionIndex
