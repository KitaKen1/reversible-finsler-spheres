module

public import Finsler.Geometry.AmbientNormalNondeg
public import Finsler.Geometry.PolygonTypes

/-! Stationary polygons under iteration and rotation of the vertices. A short polygon without
zero edges at which the derivative of the Hilbert coordinate energy vanishes is stationary
along all differentiable curves of sphere polygons: the polygon energy with normalized vertices
dominates the coordinate energy composed with the coordinates of the normalization, with
equality at the polygon. Hence the iterates of a short stationary polygon without zero edges
are stationary. The rotation of the vertices of a polygon by s keeps shortness, nonzero edges
and stationarity, it commutes with iteration, and the polygon energy with normalized vertices
and the penalized energy are invariant under the rotation of ambient polygons, which is a
linear equivalence. Two bilinear functions related by a linear equivalence have kernels of the
same dimension. Hence the nullity of a short stationary polygon without zero edges is
invariant under rotation of the vertices. -/

@[expose] public section

namespace Finsler.AmbientRotation

open Module Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty Finsler.AmbientDescent
open Finsler.AmbientHessian Finsler.AmbientSymmetry Finsler.AmbientNormalIndex
open Finsler.AmbientNullity Finsler.AmbientNormalNondeg Finsler.PolygonChart
open Finsler.PolygonIterateReduction Finsler.IndexComparison Finsler.PolygonEnergyGlobal
open Finsler.SphereCoordinateEuler
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

/-! ### Kernels of bilinear functions related by a linear equivalence -/

section Kernel

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']

/-- Two bilinear functions related by a linear equivalence have kernels of the same
dimension. -/
theorem finrank_ker_congr (e : E ≃ₗ[ℝ] E') {β : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} {β' : E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ}
    (h : ∀ v w, β' (e v) (e w) = β v w) :
    finrank ℝ (LinearMap.ker β') = finrank ℝ (LinearMap.ker β) := by
  have hmap : (LinearMap.ker β).map (e : E →ₗ[ℝ] E') = LinearMap.ker β' := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hv
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun y => ?_
      obtain ⟨w, rfl⟩ := e.surjective y
      change β' (e v) (e w) = 0
      rw [h, hv]
      rfl
    · intro hx
      rw [LinearMap.mem_ker] at hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      refine LinearMap.ext fun w => ?_
      rw [← h, e.apply_symm_apply, hx]
      rfl
  rw [← hmap]
  exact LinearEquiv.finrank_map_eq e _

end Kernel

variable {n N : ℕ} [NeZero N]

/-! ### Stationary polygons and their iterates -/

/-- The penalized energy with weight zero is the polygon energy with normalized vertices. -/
theorem pen_zero (F : ReversibleMetric n) : pen F N 0 = polyEnergyN F N := by
  funext Q
  unfold pen
  rw [zero_mul, add_zero]

/-- A short polygon without zero edges at which the derivative of the Hilbert coordinate
energy vanishes is stationary along all differentiable curves of sphere polygons. -/
theorem polyCritical_of_fderiv_energy (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)
    (h₁ : fderiv ℝ (PolygonChart.energy F q) (base q) = 0) : PolyCritical F N q := by
  have hf₁ : ContDiffAt ℝ 2 (PolygonChart.energy F q) (base q) :=
    (energy_contDiffAt F hδ hq hne).of_le (by norm_num)
  have hE : ContDiffAt ℝ 2 (polyEnergyN F N) (amb q) :=
    (polyEnergyN_contDiffAt F hδ hq hne).of_le (by norm_num)
  have hρ : HasFDerivAt (chartN q) (fderiv ℝ (chartN q) (amb q)) (amb q) :=
    ((chartN_contDiffAt q).differentiableAt (by simp)).hasFDerivAt
  have hρ0 : chartN q (amb q) = base q := chartN_amb q
  have hle : ∀ᶠ Q in 𝓝 (amb q), PolygonChart.energy F q (chartN q Q) ≤ polyEnergyN F N Q := by
    filter_upwards [eventually_decode_chartN q] with Q hQ
    have h1 : PolygonChart.energy F q (chartN q Q) = polyEnergyN F N Q := by
      unfold PolygonChart.energy
      rw [hQ, polyEnergyN_eq_normalize F Q]
      exact polyEnergyN_eq F N (fun i => norm_coe (SphereRetraction.normalize (Q i)))
    rw [h1]
  have heq : PolygonChart.energy F q (base q) = polyEnergyN F N (amb q) := by
    have h := pen_decode F 0 q (base q)
    rw [pen_zero, decode_base] at h
    exact h.symm
  have h₂ : fderiv ℝ (polyEnergyN F N) (amb q) = 0 :=
    fderiv_eq_zero_of_le hρ0 (hf₁.differentiableAt (by simp)) (hE.differentiableAt (by simp))
      h₁ hρ hle heq
  have hd := (hE.differentiableAt (by simp)).hasFDerivAt
  rw [h₂] at hd
  exact polyCritical_of_hasFDerivAt F hd

/-- The iterates of a short stationary polygon without zero edges are stationary. -/
theorem polyCritical_iterate (m : ℕ) [NeZero m] (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)
    (hc : PolyCritical F N q) : PolyCritical F (m * N) (iterate m N q) := by
  have hcrit := fderiv_energy_eq_zero_of_polyCritical F hδ hq hne hc
  exact polyCritical_of_fderiv_energy F hδ (shortPolygon_iterate m N hq) (iterate_ne m N hne)
    ((Hessian.gradient_eq_zero_iff _ _).mp
      (PolygonTypes.grad_iterate_eq_zero_of_grad F hδ hq hne m
        ((Hessian.gradient_eq_zero_iff _ _).mpr hcrit)))

/-! ### Rotation of the vertices -/

/-- The rotation of the vertices of a polygon by s. -/
def rotP {α : Type*} (s : ZMod N) (q : ZMod N → α) : ZMod N → α := fun i => q (i + s)

omit [NeZero N] in
theorem rotP_apply {α : Type*} (s : ZMod N) (q : ZMod N → α) (i : ZMod N) :
    rotP s q i = q (i + s) := rfl

omit [NeZero N] in
theorem amb_rotP (s : ZMod N) (q : ZMod N → Sphere n) : amb (rotP s q) = rotA N s (amb q) := rfl

omit [NeZero N] in
theorem shortPolygon_rotP {δ : ℝ} (s : ZMod N) {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    ShortPolygon δ (rotP s q) := fun i => by
  rw [rotP_apply, rotP_apply, add_right_comm]
  exact hq (i + s)

omit [NeZero N] in
theorem rotP_ne (s : ZMod N) {q : ZMod N → Sphere n} (hne : ∀ i, q (i + 1) ≠ q i) (i : ZMod N) :
    rotP s q (i + 1) ≠ rotP s q i := by
  rw [rotP_apply, rotP_apply, add_right_comm]
  exact hne (i + s)

omit [NeZero N] in
/-- Rotation of the vertices commutes with iteration. -/
theorem iterate_rotP {α : Type*} (m : ℕ) [NeZero m] (k : ℕ) (q : ZMod N → α) :
    iterate m N (rotP (k : ZMod N) q) = rotP (k : ZMod (m * N)) (iterate m N q) := by
  funext i
  rw [iterate_apply, rotP_apply, rotP_apply, iterate_apply, map_add, red_natCast]

/-- The rotation of ambient polygons as a linear equivalence. -/
def rotE (s : ZMod N) : (ZMod N → Ambient n) ≃ₗ[ℝ] (ZMod N → Ambient n) where
  toFun := rotA N s
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := rotA N (-s)
  left_inv := fun Q => by rw [rotA_rotA, neg_add_cancel, rotA_zero]
  right_inv := fun Q => by rw [rotA_rotA, add_neg_cancel, rotA_zero]

omit [NeZero N] in
theorem rotE_apply (s : ZMod N) (Q : ZMod N → Ambient n) : rotE s Q = rotA N s Q := rfl

/-- The second derivative of the penalized energy is natural under rotation. -/
theorem sndDeriv_pen_rotA (F : ReversibleMetric n) (lam : ℝ) (s : ZMod N)
    {Q : ZMod N → Ambient n} (hf : ContDiffAt ℝ 2 (pen F N lam) (rotA N s Q))
    (v w : ZMod N → Ambient n) :
    fderiv ℝ (fderiv ℝ (pen F N lam)) (rotA N s Q) (rotA N s v) (rotA N s w) =
      fderiv ℝ (fderiv ℝ (pen F N lam)) Q v w := by
  have h := sndDeriv_comp_linear (rotA (n := n) N s) hf v w
  have he : pen F N lam ∘ rotA (n := n) N s = pen F N lam := funext fun x => pen_rotA N F lam s x
  rw [he] at h
  exact h.symm

/-- The rotation of the vertices of a stationary polygon is stationary. -/
theorem polyCritical_rotP (F : ReversibleMetric n) {q : ZMod N → Sphere n}
    (hc : PolyCritical F N q) (s : ZMod N) : PolyCritical F N (rotP s q) := by
  intro c c' hc0 hcn hcd
  have hc0' : (fun r : ℝ => rotA N (-s) (c r)) 0 = fun i => ((q i : Sphere n) : Ambient n) := by
    change rotA N (-s) (c 0) = _
    rw [hc0]
    funext i
    change ((rotP s q (i + -s) : Sphere n) : Ambient n) = _
    rw [rotP_apply, neg_add_cancel_right]
  have hcn' : ∀ r i, ‖(fun r : ℝ => rotA N (-s) (c r)) r i‖ = 1 := fun r i => hcn r (i + -s)
  have hcd' : HasDerivAt (fun r : ℝ => rotA N (-s) (c r)) (rotA N (-s) c') 0 :=
    (rotA (n := n) N (-s)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcd
  have h := hc _ _ hc0' hcn' hcd'
  have he : (fun r => polyEnergy F N (c r)) =
      fun r => polyEnergy F N ((fun r : ℝ => rotA N (-s) (c r)) r) := by
    funext r
    have h1 := pen_rotA N F 0 (-s) (c r)
    rw [pen_zero] at h1
    rw [← polyEnergyN_eq F N (hcn r), ← h1]
    exact polyEnergyN_eq F N (hcn' r)
  rw [he]
  exact h

/-- **The nullity is invariant under rotation of the vertices.** -/
theorem nullity_rotP (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)
    (hc : PolyCritical F N q) (s : ZMod N) : nullity F (rotP s q) = nullity F q := by
  have hq' := shortPolygon_rotP s hq
  have hne' := rotP_ne s hne
  have hc' := polyCritical_rotP F hc s
  rw [← finrank_ker_sndDeriv_pen F hδ hq' hne' hc' one_pos,
    ← finrank_ker_sndDeriv_pen F hδ hq hne hc one_pos]
  have hf : ContDiffAt ℝ 2 (pen F N 1) (rotA N s (amb q)) := by
    rw [← amb_rotP]
    exact pen_contDiffAt_two F hδ hq' hne' 1
  refine finrank_ker_congr (rotE s) fun v w => ?_
  rw [amb_rotP]
  exact sndDeriv_pen_rotA F 1 s hf v w

end

end Finsler.AmbientRotation
