module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import Finsler.Analysis.FrameField
public import Mathlib.Topology.TietzeExtension

/-! Smooth approximation compatible with linear involutions. Approximate first by the existing
Mathlib theorem, then average. Equivariance is exact and the approximation error is controlled
using the operator norm of the target involution. In particular this does not require a norm
for which that involution is isometric. Application to definite frames still requires a
continuous equivariant frame and a sufficiently small error on the critical circle. -/

@[expose] public section

namespace Finsler.EquivariantApprox

open Set
open scoped ContDiff

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (τ : E →L[ℝ] E) (σ : V →L[ℝ] V)

/-- Averaging over the two-element group, with its action on the target. -/
def average (G : E → V) (x : E) : V := (1 / 2 : ℝ) • (G x + σ (G (τ x)))

/-- The averaged map is exactly equivariant. -/
theorem average_equivariant (hτ : ∀ x, τ (τ x) = x) (hσ : ∀ v, σ (σ v) = v)
    (G : E → V) (x : E) : average τ σ G (τ x) = σ (average τ σ G x) := by
  simp only [average, hτ, map_smul, map_add, hσ]
  rw [add_comm]

/-- Averaging preserves a map at every point where it already satisfies equivariance. -/
theorem average_eq (hσ : ∀ v, σ (σ v) = v) {G : E → V} {x : E}
    (hG : G (τ x) = σ (G x)) : average τ σ G x = G x := by
  rw [average, hG, hσ]
  module

/-- Averaging preserves smoothness. -/
theorem average_contDiff {G : E → V} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (average τ σ G) :=
  (hG.add (σ.contDiff.comp (hG.comp τ.contDiff))).const_smul _

/-- Averaging also preserves continuity before smooth approximation. -/
theorem average_continuous {G : E → V} (hG : Continuous G) : Continuous (average τ σ G) :=
  (hG.add (σ.continuous.comp (hG.comp τ.continuous))).const_smul _

/-- An explicit error estimate for averaging an approximation to an equivariant map. -/
theorem norm_average_sub_le (hσ : ∀ v, σ (σ v) = v) {f G : E → V}
    {x : E} (hf : f (τ x) = σ (f x)) {δ : ℝ}
    (hG : ‖G x - f x‖ ≤ δ) (hGτ : ‖G (τ x) - f (τ x)‖ ≤ δ) :
    ‖average τ σ G x - f x‖ ≤ (1 / 2 : ℝ) * (1 + ‖σ‖) * δ := by
  have he : average τ σ G x - f x =
      (1 / 2 : ℝ) • ((G x - f x) + σ (G (τ x) - f (τ x))) := by
    rw [average, map_sub, hf, hσ]
    module
  rw [he, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h1 : ‖σ (G (τ x) - f (τ x))‖ ≤ ‖σ‖ * δ :=
    (σ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hGτ (norm_nonneg _))
  have h2 := (norm_add_le (G x - f x) (σ (G (τ x) - f (τ x)))).trans
    (add_le_add hG h1)
  nlinarith

variable [FiniteDimensional ℝ E]

/-- **Smooth equivariant approximation.** Every continuous equivariant map between a
finite-dimensional real vector space with a linear involution and a real normed space with a
linear involution has uniformly close smooth equivariant approximations. -/
theorem exists_smooth_equivariant_approx (hτ : ∀ x, τ (τ x) = x)
    (hσ : ∀ v, σ (σ v) = v) {f : E → V} (hf : Continuous f)
    (heq : ∀ x, f (τ x) = σ (f x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → V, ContDiff ℝ ∞ G ∧ (∀ x, G (τ x) = σ (G x)) ∧
      ∀ x, ‖G x - f x‖ < ε := by
  have hden : 0 < 1 + ‖σ‖ := by linarith [norm_nonneg σ]
  have hδ : 0 < ε / (1 + ‖σ‖) := div_pos hε hden
  obtain ⟨G, hG, happ, -⟩ := hf.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => ε / (1 + ‖σ‖)) continuous_const (fun _ => hδ)
  refine ⟨average τ σ G, average_contDiff τ σ hG, average_equivariant τ σ hτ hσ G, ?_⟩
  intro x
  have ha : ‖G x - f x‖ ≤ ε / (1 + ‖σ‖) := by
    simpa only [dist_eq_norm] using (happ x).le
  have hb : ‖G (τ x) - f (τ x)‖ ≤ ε / (1 + ‖σ‖) := by
    simpa only [dist_eq_norm] using (happ (τ x)).le
  have h := norm_average_sub_le τ σ hσ (heq x) ha hb
  have hc : (1 / 2 : ℝ) * (1 + ‖σ‖) * (ε / (1 + ‖σ‖)) = ε / 2 := by
    field_simp
  rw [hc] at h
  exact h.trans_lt (by linarith)

section Frames

open Finsler.DefiniteFrames Finsler.FrameField Metric Topology

variable {b : ℕ}

/-- **Equivariant smoothing near a compact set of definite frames.** A continuous frame field
which is negative and equivariant on a compact invariant set can be smoothed and made exactly
equivariant, while remaining negative on an invariant open neighbourhood. The involution on the
frame space can combine an ambient symmetry with a diagonal change of signs. This theorem does
not construct the continuous adapted frame on the critical circle. -/
theorem exists_equivariant_negative_field
    (S : (Fin b → V) →L[ℝ] (Fin b → V))
    (hτ : ∀ x, τ (τ x) = x) (hS : ∀ v, S (S v) = v)
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hKτ : ∀ x ∈ K, τ x ∈ K)
    (Q : E → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ContinuousOn (fun p : E × V × V => Q p.1 p.2.1 p.2.2) (O ×ˢ univ))
    {f : E → Fin b → V} (hf : Continuous f)
    (heq : ∀ x ∈ K, f (τ x) = S (f x)) (hneg : ∀ x ∈ K, Neg (Q x) (f x)) :
    ∃ (G : E → Fin b → V) (U : Set E), ContDiff ℝ ∞ G ∧
      (∀ x, G (τ x) = S (G x)) ∧ IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
      (∀ x, τ x ∈ U ↔ x ∈ U) ∧ ∀ x ∈ U, Neg (Q x) (G x) := by
  let f' : E → Fin b → V := average τ S f
  have hf' : Continuous f' := average_continuous τ S hf
  have heq' : ∀ x, f' (τ x) = S (f' x) := average_equivariant τ S hτ hS f
  have hneg' : ∀ x ∈ K, Neg (Q x) (f' x) := by
    intro x hx
    change Neg (Q x) (average τ S f x)
    rw [average_eq τ S hS (heq x hx)]
    exact hneg x hx
  have hgraph := hK.image (continuous_id.prodMk hf')
  have hsub : (fun x : E => (x, f' x)) '' K ⊆
      {p : E × (Fin b → V) | p.1 ∈ O ∧ Neg (Q p.1) p.2} := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hKO hx, hneg' x hx⟩
  obtain ⟨δ, hδ, hthick⟩ := hgraph.exists_thickening_subset_open (isOpen_pairs hO Q hQ) hsub
  obtain ⟨G, hG, hGeq, happ⟩ := exists_smooth_equivariant_approx τ S hτ hS hf' heq' hδ
  have hGK : ∀ x ∈ K, x ∈ O ∧ Neg (Q x) (G x) := by
    intro x hx
    change (x, G x) ∈ {p : E × (Fin b → V) | p.1 ∈ O ∧ Neg (Q p.1) p.2}
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨(x, f' x), ⟨x, hx, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    exact happ x
  let W : Set E := {x | x ∈ O ∧ Neg (Q x) (G x)}
  have hW : IsOpen W := (isOpen_pairs hO Q hQ).preimage
    (continuous_id.prodMk hG.continuous)
  refine ⟨G, W ∩ τ ⁻¹' W, hG, hGeq, hW.inter (hW.preimage τ.continuous),
    fun x hx => ⟨hGK x hx, hGK (τ x) (hKτ x hx)⟩,
    fun _ hx => hx.1.1, ?_, fun _ hx => hx.1.2⟩
  intro x
  change (τ x ∈ W ∧ τ (τ x) ∈ W) ↔ (x ∈ W ∧ τ x ∈ W)
  rw [hτ, and_comm]

/-- **Equivariant extension of definite frames from a compact invariant set.** Finite-dimensional
Tietze extension gives a continuous ambient field. Averaging and smooth approximation then give
an exactly equivariant smooth field, negative on an invariant open neighbourhood of the original
compact set. The extension need not agree pointwise with the original continuous frame. -/
theorem exists_equivariant_negative_extension [FiniteDimensional ℝ V]
    (S : (Fin b → V) →L[ℝ] (Fin b → V))
    (hτ : ∀ x, τ (τ x) = x) (hS : ∀ v, S (S v) = v)
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hKτ : ∀ x ∈ K, τ x ∈ K)
    (Q : E → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ContinuousOn (fun p : E × V × V => Q p.1 p.2.1 p.2.2) (O ×ˢ univ))
    (f : C(K, Fin b → V))
    (heq : ∀ x : K, f ⟨τ x, hKτ x x.2⟩ = S (f x))
    (hneg : ∀ x : K, Neg (Q x) (f x)) :
    ∃ (G : E → Fin b → V) (U : Set E), ContDiff ℝ ∞ G ∧
      (∀ x, G (τ x) = S (G x)) ∧ IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
      (∀ x, τ x ∈ U ↔ x ∈ U) ∧ ∀ x ∈ U, Neg (Q x) (G x) := by
  let e := (Module.finBasis ℝ (Fin b → V)).equivFunL
  let : TietzeExtension (Fin b → V) := TietzeExtension.of_homeo e.toHomeomorph
  obtain ⟨g, hg⟩ := f.exists_restrict_eq hK.isClosed
  have hgf : ∀ (x : E) (hx : x ∈ K), g x = f ⟨x, hx⟩ := by
    intro x hx
    exact congrArg (fun k : C(K, Fin b → V) => k ⟨x, hx⟩) hg
  apply exists_equivariant_negative_field τ S hτ hS hK hO hKO hKτ Q hQ g.continuous
  · intro x hx
    rw [hgf (τ x) (hKτ x hx), hgf x hx]
    exact heq ⟨x, hx⟩
  · intro x hx
    rw [hgf x hx]
    exact hneg ⟨x, hx⟩

end Frames

end

end Finsler.EquivariantApprox
