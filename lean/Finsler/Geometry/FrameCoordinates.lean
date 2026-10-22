module

public import Finsler.Geometry.CircleFrameField
public import Finsler.Analysis.NormalExpansion

/-! Frame coordinates near a circle of iterated polygons and the split descent estimate. Let
G₁ and G₂ be smooth fields of b and p vectors of the normal space of the iterated polygons with
m N vertices, defined on the ambient polygons with N vertices. The frame coordinates of a root
polygon z and coefficients (x, y) are the m-fold iterate of z plus the combinations of G₁(z)
with x and of G₂(z) with y; the composite Ψ of the penalized energy with the frame coordinates
is C³ where the penalized energy is C³. The first derivative of the penalized energy at an
iterated polygon vanishes on the normal space (it is invariant under the rotation by one
period), so the fibre derivative of Ψ vanishes on the zero section, and the second fibre
derivative of Ψ at (z, 0) is the second derivative of the penalized energy at the iterate on
the frame combinations (the frame coordinates are affine in the fibre). If G₁(z) is a negative
and G₂(z) a positive frame for the normal second derivative at every z of a compact set K₀,
then for J(x, y) = (x, -y) the cross terms cancel and, by compactness,

  D²Ψ(z, 0)((0, ξ), (0, J ξ)) ≤ -2c ‖ξ‖²  for z in K₀.

By the expansion along the fibres (v0.109) there are R, κ > 0 such that for z in K₀,
‖ξ‖ ≤ R and base vectors v with ‖v‖ ≤ κ

  DΨ(z, ξ)(v, J ξ) ≤ DΨ(z, 0)(v, 0) - c ‖ξ‖²,

which makes the split field (v, J ξ) a descent direction off the zero section. -/

@[expose] public section

namespace Finsler.FrameCoordinates

open Module Filter Set
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.NormalExpansion
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

/-! ### Affine compositions -/

section Affine

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]

/-- The derivative of a composition with an affine map. -/
theorem fderiv_comp_affine {f : E₂ → ℝ} (a : E₂) (L : E₁ →L[ℝ] E₂) {p : E₁}
    (hf : DifferentiableAt ℝ f (a + L p)) (v : E₁) :
    fderiv ℝ (fun x => f (a + L x)) p v = fderiv ℝ f (a + L p) (L v) := by
  have h : HasFDerivAt (fun x => a + L x) L p := L.hasFDerivAt.const_add a
  have h1 := (hf.hasFDerivAt.comp p h).fderiv
  exact congrArg (fun φ : E₁ →L[ℝ] ℝ => φ v) h1

/-- The second derivative of a composition with an affine map. -/
theorem sndDeriv_comp_affine {f : E₂ → ℝ} (a : E₂) (L : E₁ →L[ℝ] E₂) {p : E₁}
    (hf : ContDiffAt ℝ 2 f (a + L p)) (v w : E₁) :
    fderiv ℝ (fderiv ℝ (fun x => f (a + L x))) p v w =
      fderiv ℝ (fderiv ℝ f) (a + L p) (L v) (L w) := by
  have ht : ContDiffAt ℝ 2 (fun y => f (a + y)) (L p) :=
    ContDiffAt.comp (g := f) (f := fun y => a + y) (L p) hf (contDiffAt_const.add contDiffAt_id)
  have h1 := sndDeriv_comp_linear L ht v w
  have e1 : (fun x => f (a + L x)) = (fun y => f (a + y)) ∘ L := rfl
  have e2 : fderiv ℝ (fun y => f (a + y)) = fun y => fderiv ℝ f (a + y) :=
    funext fun y => fderiv_comp_add_left a
  have e3 : fderiv ℝ (fun y => fderiv ℝ f (a + y)) (L p) = fderiv ℝ (fderiv ℝ f) (a + L p) :=
    fderiv_comp_add_left a
  rw [e1, h1, e2, e3]

end Affine

/-! ### A uniform bound for negative frames on a compact set -/

section Bound

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {b : ℕ}

omit [NormedSpace ℝ E] in
/-- A continuous field of negative frames over a compact set is uniformly negative. -/
theorem exists_neg_bound (Q : E → V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {S : Set E}
    (hQ : ContinuousOn (fun q : E × V × V => Q q.1 q.2.1 q.2.2) (S ×ˢ univ))
    {G : E → Fin b → V} (hG : Continuous G) {K : Set E} (hK : IsCompact K) (hKS : K ⊆ S)
    (hneg : ∀ z ∈ K, Neg (Q z) (G z)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ u : Fin b → ℝ,
      Q z (comb (G z) u) (comb (G z) u) ≤ -c * ‖u‖ ^ 2 := by
  have hφ : ContinuousOn (fun q : E × (Fin b → ℝ) =>
      Q q.1 (comb (G q.1) q.2) (comb (G q.1) q.2)) (K ×ˢ univ) := by
    have hc : Continuous fun q : E × (Fin b → ℝ) => comb (G q.1) q.2 :=
      comb_continuous.comp ((hG.comp continuous_fst).prodMk continuous_snd)
    refine hQ.comp (continuous_fst.prodMk (hc.prodMk hc)).continuousOn ?_
    rintro q ⟨hq, -⟩
    exact ⟨hKS hq, mem_univ _⟩
  have hzero : ∀ z, Q z (comb (G z) 0) (comb (G z) 0) = 0 := by
    intro z
    have h0 : comb (G z) (0 : Fin b → ℝ) = 0 := by simp [comb]
    rw [h0, map_zero]
  have hscale : ∀ z (u : Fin b → ℝ), u ≠ 0 → Q z (comb (G z) u) (comb (G z) u) =
      ‖u‖ ^ 2 * Q z (comb (G z) (‖u‖⁻¹ • u)) (comb (G z) (‖u‖⁻¹ • u)) := by
    intro z u hu
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    rw [comb_smul, form_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_mul]
  have hsph : ∀ u : Fin b → ℝ, u ≠ 0 → ‖u‖⁻¹ • u ∈ Metric.sphere (0 : Fin b → ℝ) 1 := by
    intro u hu
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  by_cases hT : (K ×ˢ Metric.sphere (0 : Fin b → ℝ) 1).Nonempty
  · obtain ⟨q₀, hq₀, hmax⟩ := (hK.prod (isCompact_sphere (0 : Fin b → ℝ) 1)).exists_isMaxOn hT
      (hφ.mono (prod_mono subset_rfl (subset_univ _)))
    have hq₀0 : q₀.2 ≠ 0 := by
      intro h
      have h1 := hq₀.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at h1
      exact zero_ne_one h1
    have hM : Q q₀.1 (comb (G q₀.1) q₀.2) (comb (G q₀.1) q₀.2) < 0 := hneg q₀.1 hq₀.1 q₀.2 hq₀0
    refine ⟨-Q q₀.1 (comb (G q₀.1) q₀.2) (comb (G q₀.1) q₀.2), by linarith, fun z hz u => ?_⟩
    by_cases hu : u = 0
    · rw [hu, hzero, norm_zero]
      simp
    · have hmem : (z, ‖u‖⁻¹ • u) ∈ K ×ˢ Metric.sphere (0 : Fin b → ℝ) 1 := ⟨hz, hsph u hu⟩
      have h1 := hmax hmem
      change Q z (comb (G z) (‖u‖⁻¹ • u)) (comb (G z) (‖u‖⁻¹ • u)) ≤
        Q q₀.1 (comb (G q₀.1) q₀.2) (comb (G q₀.1) q₀.2) at h1
      rw [hscale z u hu]
      have h2 : 0 ≤ ‖u‖ ^ 2 := by positivity
      nlinarith
  · refine ⟨1, one_pos, fun z hz u => ?_⟩
    by_cases hu : u = 0
    · rw [hu, hzero, norm_zero]
      simp
    · have hmem : (z, ‖u‖⁻¹ • u) ∈ K ×ˢ Metric.sphere (0 : Fin b → ℝ) 1 := ⟨hz, hsph u hu⟩
      exact (hT ⟨_, hmem⟩).elim

end Bound

/-! ### Two inequalities -/

/-- The square of the norm of a pair is at most the sum of the squares of the norms. -/
theorem sq_norm_prod_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    (q : E₁ × E₂) : ‖q‖ ^ 2 ≤ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
  have h1 := sq_nonneg ‖q.1‖
  have h2 := sq_nonneg ‖q.2‖
  rcases max_choice ‖q.1‖ ‖q.2‖ with h | h
  · rw [Prod.norm_def, h]
    linarith
  · rw [Prod.norm_def, h]
    linarith

/-- The final inequality of the split estimate. -/
theorem split_ineq {a b x y s c₁ c₂ c₀ : ℝ} (ha : a ≤ -c₁ * x) (hb : -b ≤ -c₂ * y)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : s ≤ x + y) (h1 : c₀ ≤ c₁) (h2 : c₀ ≤ c₂) (hc₀ : 0 < c₀) :
    a - b ≤ -(2 * (c₀ / 2)) * s := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hx, mul_nonneg (sub_nonneg.mpr h2) hy,
    mul_nonneg hc₀.le (sub_nonneg.mpr hs)]

/-! ### The first derivative on the normal space -/

section Normal

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n)

/-- The first derivative of the penalized energy at an iterated polygon vanishes on the normal
space. -/
theorem fderiv_pen_normal (lam : ℝ) {z : ZMod N → Ambient n}
    (hf : DifferentiableAt ℝ (pen F (m * N) lam) (iterA m N z)) {w : ZMod (m * N) → Ambient n}
    (hw : w ∈ normal (rotL (n := n) m N) m) :
    fderiv ℝ (pen F (m * N) lam) (iterA m N z) w = 0 := by
  have hp : rotA (m * N) (N : ZMod (m * N)) (iterA m N z) = iterA m N z := rotA_iterate m N z
  have hinv : ∀ v, fderiv ℝ (pen F (m * N) lam) (iterA m N z) (rotL m N v) =
      fderiv ℝ (pen F (m * N) lam) (iterA m N z) v := by
    intro v
    have he : pen F (m * N) lam ∘ rotA (n := n) (m * N) (N : ZMod (m * N)) = pen F (m * N) lam :=
      funext fun x => pen_rotA (m * N) F lam _ x
    have hf' : DifferentiableAt ℝ (pen F (m * N) lam)
        (rotA (m * N) (N : ZMod (m * N)) (iterA m N z)) := by
      rw [hp]
      exact hf
    have h1 := (hf'.hasFDerivAt.comp (iterA m N z)
      (rotA (n := n) (m * N) (N : ZMod (m * N))).hasFDerivAt).fderiv
    rw [he, hp] at h1
    rw [rotL_apply]
    exact (congrArg (fun φ : (ZMod (m * N) → Ambient n) →L[ℝ] ℝ => φ v) h1).symm
  have hpow : ∀ j : ℕ, fderiv ℝ (pen F (m * N) lam) (iterA m N z)
      (((rotL (n := n) m N) ^ j) w) = fderiv ℝ (pen F (m * N) lam) (iterA m N z) w := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', Module.End.mul_apply, hinv, ih]
  rw [mem_normal, powSum_apply] at hw
  have hsum := congrArg (fderiv ℝ (pen F (m * N) lam) (iterA m N z)) hw
  rw [map_sum, map_zero] at hsum
  simp only [hpow, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  exact (mul_eq_zero.mp hsum).resolve_left hm

end Normal

/-! ### Frame coordinates -/

section Coordinates

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)

/-- The fibre part of the frame coordinates at a root polygon. -/
def fibreL (z : ZMod N → Ambient n) :
    (Fin b → ℝ) × (Fin p → ℝ) →L[ℝ] (ZMod (m * N) → Ambient n) :=
  (∑ i, ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Fin b → ℝ) (Fin p → ℝ))).smulRight
        ((G₁ z i : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n)) +
    ∑ j, ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (Fin b → ℝ) (Fin p → ℝ))).smulRight
        ((G₂ z j : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n)

theorem fibreL_apply (z : ZMod N → Ambient n) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    fibreL m N G₁ G₂ z ξ =
      ((comb (G₁ z) ξ.1 : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) +
        ((comb (G₂ z) ξ.2 : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) := by
  simp only [fibreL, add_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    comb, Submodule.coe_sum, Submodule.coe_smul]

theorem fibreL_mem (z : ZMod N → Ambient n) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    fibreL m N G₁ G₂ z ξ ∈ normal (rotL (n := n) m N) m := by
  rw [fibreL_apply]
  exact Submodule.add_mem _ (Submodule.coe_mem _) (Submodule.coe_mem _)

/-- The frame coordinates. -/
def coord (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) : ZMod (m * N) → Ambient n :=
  iterA m N q.1 + fibreL m N G₁ G₂ q.1 q.2

/-- The penalized energy in frame coordinates. -/
def psi (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) : ℝ :=
  pen F (m * N) 1 (coord m N G₁ G₂ q)

omit [NeZero m] [NeZero N] in
theorem coord_zero (z : ZMod N → Ambient n) : coord m N G₁ G₂ (z, 0) = iterA m N z := by
  unfold coord
  rw [map_zero, add_zero]

theorem coord_contDiff (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂) :
    ContDiff ℝ ∞ (coord m N G₁ G₂) := by
  have h : coord m N G₁ G₂ = fun q => iterA m N q.1 +
      ((∑ i, q.2.1 i • (normal (rotL (n := n) m N) m).subtypeL (G₁ q.1 i)) +
        ∑ j, q.2.2 j • (normal (rotL (n := n) m N) m).subtypeL (G₂ q.1 j)) := by
    funext q
    unfold coord
    rw [fibreL_apply]
    simp only [comb, Submodule.coe_sum, Submodule.coe_smul, Submodule.subtypeL_apply]
  rw [h]
  refine ((iterA (n := n) m N).contDiff.comp contDiff_fst).add
    ((ContDiff.sum fun i _ => ?_).add (ContDiff.sum fun j _ => ?_))
  · exact ((contDiff_apply ℝ ℝ i).comp (contDiff_fst.comp contDiff_snd)).smul
      ((normal (rotL (n := n) m N) m).subtypeL.contDiff.comp
        ((contDiff_apply ℝ (normal (rotL (n := n) m N) m) i).comp (hG₁.comp contDiff_fst)))
  · exact ((contDiff_apply ℝ ℝ j).comp (contDiff_snd.comp contDiff_snd)).smul
      ((normal (rotL (n := n) m N) m).subtypeL.contDiff.comp
        ((contDiff_apply ℝ (normal (rotL (n := n) m N) m) j).comp (hG₂.comp contDiff_fst)))

/-- The penalized energy along a fibre of the frame coordinates. -/
theorem psi_fibre (z : ZMod N → Ambient n) :
    (fun ξ : (Fin b → ℝ) × (Fin p → ℝ) =>
      psi m N F G₁ G₂ ((z, 0) + ContinuousLinearMap.inr ℝ (ZMod N → Ambient n)
        ((Fin b → ℝ) × (Fin p → ℝ)) ξ)) =
      fun ξ => pen F (m * N) 1 (iterA m N z + fibreL m N G₁ G₂ z ξ) := by
  funext ξ
  simp only [psi, coord, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

/-- The swap of the signs of the positive coefficients. -/
def swapJ : (Fin b → ℝ) × (Fin p → ℝ) →L[ℝ] (Fin b → ℝ) × (Fin p → ℝ) :=
  (ContinuousLinearMap.id ℝ (Fin b → ℝ)).prodMap (-ContinuousLinearMap.id ℝ (Fin p → ℝ))

omit [NeZero m] [NeZero N] in
theorem swapJ_apply (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    swapJ (b := b) (p := p) ξ = (ξ.1, -ξ.2) := rfl

/-- **The split descent estimate in frame coordinates.** If on a compact set K₀ of root
polygons, at whose iterates the penalized energy is C³, the fields G₁ and G₂ are negative and
positive frames for the normal second derivative, there are R, κ, c > 0 such that for z in K₀,
‖ξ‖ ≤ R and base vectors v with ‖v‖ ≤ κ the penalized energy is C³ at the frame coordinates
of (z, ξ) and DΨ(z, ξ)(v, J ξ) ≤ DΨ(z, 0)(v, 0) - c ‖ξ‖². -/
theorem exists_split_descent_coord (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K₀ : Set (ZMod N → Ambient n)} (hK : IsCompact K₀) (hKs : K₀ ⊆ smoothSet m N F)
    (hneg₁ : ∀ z ∈ K₀, Neg (normalForm m N F z) (G₁ z))
    (hneg₂ : ∀ z ∈ K₀, Neg (-normalForm m N F z) (G₂ z)) :
    ∃ R κ c : ℝ, 0 < R ∧ 0 < κ ∧ 0 < c ∧ ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ),
      ‖ξ‖ ≤ R → ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2 := by
  have hcoord := coord_contDiff m N G₁ G₂ hG₁ hG₂
  -- the open set where the penalized energy is C³ at the coordinates
  have hopen : IsOpen {y : ZMod (m * N) → Ambient n | ContDiffAt ℝ 3 (pen F (m * N) 1) y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact ContDiffAt.eventually hy (by simp)
  set 𝒪 : Set ((ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :=
    coord m N G₁ G₂ ⁻¹' {y | ContDiffAt ℝ 3 (pen F (m * N) 1) y} with h𝒪def
  have h𝒪 : IsOpen 𝒪 := hopen.preimage hcoord.continuous
  have hpsiAt : ∀ q ∈ 𝒪, ContDiffAt ℝ 3 (psi m N F G₁ G₂) q := fun q hq =>
    ContDiffAt.comp (g := pen F (m * N) 1) (f := coord m N G₁ G₂) q hq
      (hcoord.contDiffAt.of_le (by simp))
  have hΨ : ContDiffOn ℝ 3 (psi m N F G₁ G₂) 𝒪 := fun q hq => (hpsiAt q hq).contDiffWithinAt
  have hsub : ∀ z ∈ K₀, (z, (0 : (Fin b → ℝ) × (Fin p → ℝ))) ∈ 𝒪 := by
    intro z hz
    change ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, 0))
    rw [coord_zero]
    exact hKs hz
  have hbase : ∀ z : ZMod N → Ambient n,
      (z, (0 : (Fin b → ℝ) × (Fin p → ℝ))) + ContinuousLinearMap.inr ℝ (ZMod N → Ambient n)
        ((Fin b → ℝ) × (Fin p → ℝ)) 0 = (z, 0) := by
    intro z
    rw [map_zero, add_zero]
  have hfib0 : ∀ z : ZMod N → Ambient n, iterA m N z + fibreL m N G₁ G₂ z 0 = iterA m N z := by
    intro z
    rw [map_zero, add_zero]
  -- the fibre derivative vanishes on the zero section
  have hcrit : ∀ z : ZMod N → Ambient n, (z, (0 : (Fin b → ℝ) × (Fin p → ℝ))) ∈ 𝒪 →
      ∀ w : (Fin b → ℝ) × (Fin p → ℝ), fderiv ℝ (psi m N F G₁ G₂) (z, 0) (0, w) = 0 := by
    intro z hz w
    have hz' : ContDiffAt ℝ 3 (pen F (m * N) 1) (iterA m N z) := by
      have h := hz
      change ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, 0)) at h
      rwa [coord_zero] at h
    have hd : DifferentiableAt ℝ (psi m N F G₁ G₂)
        ((z, 0) + ContinuousLinearMap.inr ℝ (ZMod N → Ambient n)
          ((Fin b → ℝ) × (Fin p → ℝ)) 0) := by
      rw [hbase]
      exact (hpsiAt _ hz).differentiableAt (by norm_num)
    have h1 := fderiv_comp_affine (z, (0 : (Fin b → ℝ) × (Fin p → ℝ)))
      (ContinuousLinearMap.inr ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ))) hd w
    rw [hbase, psi_fibre] at h1
    have hd2 : DifferentiableAt ℝ (pen F (m * N) 1) (iterA m N z + fibreL m N G₁ G₂ z 0) := by
      rw [hfib0]
      exact hz'.differentiableAt (by norm_num)
    have h2 := fderiv_comp_affine (iterA m N z) (fibreL m N G₁ G₂ z) hd2 w
    rw [hfib0] at h2
    change fderiv ℝ (psi m N F G₁ G₂) (z, 0)
      (ContinuousLinearMap.inr ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ)) w) = 0
    rw [← h1, h2]
    exact fderiv_pen_normal m N F 1 (hz'.differentiableAt (by norm_num)) (fibreL_mem m N G₁ G₂ z w)
  -- uniform negativity of the frames
  have hG₁c : Continuous G₁ := hG₁.continuous
  have hG₂c : Continuous G₂ := hG₂.continuous
  obtain ⟨c₁, hc₁, hb₁⟩ := exists_neg_bound (normalForm m N F)
    (normalForm_continuousOn m N F) hG₁c hK hKs hneg₁
  obtain ⟨c₂, hc₂, hb₂⟩ := exists_neg_bound (fun z => -normalForm m N F z)
    (normalForm_continuousOn m N F).neg hG₂c hK hKs hneg₂
  obtain ⟨c₀, hc₀1, hc₀2, hc₀⟩ : ∃ c₀ : ℝ, c₀ ≤ c₁ ∧ c₀ ≤ c₂ ∧ 0 < c₀ :=
    ⟨min c₁ c₂, min_le_left _ _, min_le_right _ _, lt_min hc₁ hc₂⟩
  have hc : 0 < c₀ / 2 := by positivity
  have hJ : ∀ z ∈ K₀, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ),
      fderiv ℝ (fderiv ℝ (psi m N F G₁ G₂)) (z, 0) (0, ξ) (0, swapJ ξ) ≤
        -(2 * (c₀ / 2)) * ‖ξ‖ ^ 2 := by
    intro z hz ξ
    have hz' : ContDiffAt ℝ 3 (pen F (m * N) 1) (iterA m N z) := hKs hz
    have h2psi : ContDiffAt ℝ 2 (psi m N F G₁ G₂)
        ((z, 0) + ContinuousLinearMap.inr ℝ (ZMod N → Ambient n)
          ((Fin b → ℝ) × (Fin p → ℝ)) 0) := by
      rw [hbase]
      exact (hpsiAt _ (hsub z hz)).of_le (by norm_num)
    have h1 := sndDeriv_comp_affine (z, (0 : (Fin b → ℝ) × (Fin p → ℝ)))
      (ContinuousLinearMap.inr ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ))) h2psi ξ
      (swapJ ξ)
    rw [hbase, psi_fibre] at h1
    have h2pen : ContDiffAt ℝ 2 (pen F (m * N) 1) (iterA m N z + fibreL m N G₁ G₂ z 0) := by
      rw [hfib0]
      exact hz'.of_le (by norm_num)
    have h2 := sndDeriv_comp_affine (iterA m N z) (fibreL m N G₁ G₂ z) h2pen ξ (swapJ ξ)
    rw [hfib0] at h2
    change fderiv ℝ (fderiv ℝ (psi m N F G₁ G₂)) (z, 0)
      (ContinuousLinearMap.inr ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ)) ξ)
      (ContinuousLinearMap.inr ℝ (ZMod N → Ambient n) ((Fin b → ℝ) × (Fin p → ℝ))
        (swapJ ξ)) ≤ _
    rw [← h1, h2]
    -- the second derivative on the frame combinations
    have hsym := (hz'.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
    set A : ZMod (m * N) → Ambient n :=
      ((comb (G₁ z) ξ.1 : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) with hA
    set B : ZMod (m * N) → Ambient n :=
      ((comb (G₂ z) ξ.2 : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) with hB
    have hL1 : fibreL m N G₁ G₂ z ξ = A + B := fibreL_apply m N G₁ G₂ z ξ
    have hL2 : fibreL m N G₁ G₂ z (swapJ ξ) = A - B := by
      rw [fibreL_apply, swapJ_apply]
      have hneg : comb (G₂ z) (-ξ.2) = -comb (G₂ z) ξ.2 := by
        have h := comb_smul (G₂ z) (-1) ξ.2
        rw [neg_one_smul, neg_one_smul] at h
        exact h
      rw [hneg, Submodule.coe_neg, ← sub_eq_add_neg]
    rw [hL1, hL2]
    have hAB : fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) B A =
        fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) A B := hsym.eq B A
    have e : fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) (A + B) (A - B) =
        fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) A A -
          fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) B B := by
      rw [map_add, map_sub]
      change (fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) A A +
          fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) B A) -
        (fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) A B +
          fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) B B) = _
      rw [hAB]
      ring
    rw [e]
    have hA1 : fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) A A ≤ -c₁ * ‖ξ.1‖ ^ 2 :=
      hb₁ z hz ξ.1
    have hB1 : -(fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z) B B) ≤ -c₂ * ‖ξ.2‖ ^ 2 :=
      hb₂ z hz ξ.2
    exact split_ineq hA1 hB1 (sq_nonneg _) (sq_nonneg _) (sq_norm_prod_le ξ) hc₀1 hc₀2 hc₀
  obtain ⟨R, κ, hR, hκ, hdesc⟩ := exists_split_descent h𝒪 hΨ hK hsub hcrit swapJ hc hJ
  refine ⟨R, κ, c₀ / 2, hR, hκ, hc, fun z hz ξ hξ => ?_⟩
  obtain ⟨hmem, hd⟩ := hdesc z hz ξ hξ
  exact ⟨hmem, hd⟩

end Coordinates

end

end Finsler.FrameCoordinates

