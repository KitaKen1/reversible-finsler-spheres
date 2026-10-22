module

public import Finsler.Geometry.CriticalLevels
public import Finsler.Analysis.IntervalH1RotationContinuity
public import Finsler.Analysis.IntervalH1ShiftEnergy
public import Finsler.Topology.BorelLocal

/-! Orientation of the critical set of a level. The H¹ loop of a rotated smooth loop is the
rotation of its H¹ loop. For a level c > 0 the positive critical loops are the rotations of the
iterates, of level c, of the chosen prime closed geodesics, and the negative ones are their
reversals; every tangent critical loop of energy c² is positive or negative. With finitely many
prime closed geodesic images both sets are compact. They are disjoint: a rotation of an iterate
of a closed geodesic is never the reversal of such a rotation, since at a fixed time of the
parameter reflection the velocity would vanish. Hence their images in the space of continuous
maps of the circle have a positive distance δ, and the loops which are uniformly within δ/4 of a
tangent critical loop of energy c² form a set oriented by the two open sets of loops uniformly
within δ/2 of a positive, respectively negative, critical loop. -/

@[expose] public section

namespace Finsler.OrientedCritical

open Set Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SmoothSobolev
open Finsler.SobolevCurveVariation Finsler.SobolevCircleRepresentative Finsler.SobolevReverse
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.SobolevShiftEnergy
open Finsler.CriticalLevels Finsler.EnergyConservation Finsler.BorelLoop Finsler.BorelLocal

noncomputable section

variable {n : ℕ}

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

/-! ### Smooth loops and the circle action -/

theorem coe_fract (s : ℝ) : ((Int.fract s : ℝ) : Circ) = (s : Circ) := by
  have h : (s : ℝ) = Int.fract s + (⌊s⌋ : ℤ) • (1 : ℝ) := by
    rw [zsmul_eq_mul, mul_one]
    exact (Int.fract_add_floor s).symm
  conv_rhs => rw [h]
  rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]

/-- The circle map of the H¹ loop of a smooth loop. -/
theorem sphereCircleMap_ofSmooth (σ : SmoothLoop n) (s : ℝ) :
    sphereCircleMap (ofSmooth σ) (s : Circ) = σ s := by
  have hmem : Int.fract s ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
  rw [← coe_fract s]
  have h := sphereCircleMap_coe (ofSmooth σ) ⟨Int.fract s, hmem⟩
  rw [sphereRepresentative_ofSmooth] at h
  exact h.trans (loop_eq_fract σ s)

/-- The H¹ loop of a rotated smooth loop is the rotation of its H¹ loop. -/
theorem ofSmooth_shift (σ : SmoothLoop n) (a : ℝ) :
    ofSmooth (shift σ a) = (a : Circ) +ᵥ ofSmooth σ := by
  apply sphereCircleMap_injective n
  apply ContinuousMap.ext
  intro x
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [sphereCircleMap_vadd, sphereCircleMap_ofSmooth, ← AddCircle.coe_add,
    sphereCircleMap_ofSmooth]
  change σ (s + a) = σ (a + s)
  rw [add_comm]

/-- The reversal of a smooth loop is not a rotation of it if the velocity does not vanish. -/
theorem reverse_ne_shift_of_deriv {γ : SmoothLoop n} (a : ℝ)
    (hne : deriv (position γ) (a / 2) ≠ 0) : reverse γ ≠ shift γ a := by
  intro h
  have hpos : ∀ t : ℝ, position γ (-t) = position γ (t + a) := fun t =>
    congrArg Subtype.val (congrArg (fun σ : SmoothLoop n => σ t) h)
  have h1 := Finsler.GeodesicUnique.affine_position_hasDerivAt γ 0 (-1) (-a / 2)
  have h2 := Finsler.GeodesicUnique.affine_position_hasDerivAt γ a 1 (-a / 2)
  have e1 : (0 : ℝ) + -a / 2 * -1 = a / 2 := by ring
  have e2 : a + -a / 2 * 1 = a / 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hfun : (fun r : ℝ => position γ (0 + r * -1)) = fun r => position γ (a + r * 1) := by
    funext r
    rw [show (0 : ℝ) + r * -1 = -r by ring, show a + r * 1 = r + a by ring]
    exact hpos r
  rw [hfun] at h1
  have heq := h1.unique h2
  rw [neg_one_smul, one_smul] at heq
  have h3 : (2 : ℝ) • deriv (position γ) (a / 2) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← heq]
    exact neg_add_cancel _
  exact hne ((smul_eq_zero.mp h3).resolve_left two_ne_zero)

/-- The velocity of a rotation of an iterate of a regular loop does not vanish. -/
theorem deriv_shift_iterate_ne_zero {γ : SmoothLoop n} (hreg : Finsler.Geodesics.Regular γ)
    {k : ℕ} (hk : k ≠ 0) (a t : ℝ) : deriv (position (shift (iterate γ k) a)) t ≠ 0 := by
  have hfun : position (shift (iterate γ k) a) =
      fun r : ℝ => position γ ((k : ℝ) * a + r * (k : ℝ)) := by
    funext r
    change ((γ ((k : ℝ) * (r + a)) : Sphere n) : Ambient n) =
      ((γ ((k : ℝ) * a + r * (k : ℝ)) : Sphere n) : Ambient n)
    rw [show (k : ℝ) * (r + a) = (k : ℝ) * a + r * (k : ℝ) by ring]
  rw [hfun, (Finsler.GeodesicUnique.affine_position_hasDerivAt γ ((k : ℝ) * a) (k : ℝ) t).deriv]
  exact smul_ne_zero (Nat.cast_ne_zero.mpr hk)
    (Finsler.PolygonCritical.deriv_position_ne_zero γ hreg _)

/-! ### The two orientations of the critical set of a level -/

/-- The positive critical loops of level c: rotations of the iterates of level c of the chosen
prime closed geodesics. -/
def posCrit (F : ReversibleMetric n) (c : ℝ) : Set (SphereLoop n) :=
  {γ | ∃ (s : Set (Sphere n)) (hs : s ∈ primeImages F) (k : ℕ) (θ : Circ), 0 < k ∧
    (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c ∧
    γ = θ +ᵥ ofSmooth (iterate (chosen F s hs).loop k)}

/-- The negative critical loops of level c: the reversals of the positive ones. -/
def negCrit (F : ReversibleMetric n) (c : ℝ) : Set (SphereLoop n) :=
  reverseSphere '' posCrit F c

theorem chosen_energy_pos (F : ReversibleMetric n) (s : Set (Sphere n))
    (hs : s ∈ primeImages F) :
    0 < Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) :=
  Real.sqrt_pos.mpr (regular_energy_pos F _ (chosen F s hs).regular)

/-- Every tangent critical loop of energy c², c > 0, is a positive or a negative critical loop
of level c. -/
theorem mem_posCrit_or_negCrit (F : ReversibleMetric n) {c : ℝ} (hc : 0 < c) (γ : SphereLoop n)
    (hγ : TangentCritical F γ) (hE : energy F γ = c ^ 2) :
    γ ∈ posCrit F c ∨ γ ∈ negCrit F c := by
  have hpos : 0 < energy F γ := by
    rw [hE]
    positivity
  have hlevel : ∀ (s : Set (Sphere n)) (hs : s ∈ primeImages F) (k : ℕ),
      energy F (ofSmooth (iterate (chosen F s hs).loop k)) = c ^ 2 →
      (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c := by
    intro s hs k hk
    rw [energy_ofSmooth, Finsler.LoopEnergy.energy_iterate] at hk
    have h1 : Real.sqrt ((k : ℝ) ^ 2 * Finsler.LoopEnergy.energy F (chosen F s hs).loop) =
        Real.sqrt (c ^ 2) := congrArg Real.sqrt hk
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k), Real.sqrt_sq hc.le] at h1
    exact h1
  obtain ⟨s, hs, k, a, hk, h | h⟩ := critical_eq_chosen_iterate F γ hγ hpos
  · left
    refine ⟨s, hs, k, (a : Circ), hk, hlevel s hs k ?_, ?_⟩
    · rw [← hE, h, ofSmooth_shift, energy_vadd]
    · rw [h, ofSmooth_shift]
  · right
    refine ⟨(a : Circ) +ᵥ ofSmooth (iterate (chosen F s hs).loop k),
      ⟨s, hs, k, (a : Circ), hk, hlevel s hs k ?_, rfl⟩, ?_⟩
    · rw [← hE, h, ← reverseSphere_ofSmooth, energy_reverseSphere, ofSmooth_shift, energy_vadd]
    · rw [h, ← reverseSphere_ofSmooth, ofSmooth_shift]

/-- The rotation orbit of a loop is compact. -/
theorem isCompact_orbit (u : SphereLoop n) : IsCompact (range (fun θ : Circ => θ +ᵥ u)) := by
  have h : Continuous ((fun p : Circ × SphereLoop n => p.1 +ᵥ p.2) ∘ fun θ : Circ => (θ, u)) :=
    (Finsler.SobolevRotation.sphere_action_continuous n).comp
      (continuous_id.prodMk continuous_const)
  exact isCompact_range h

/-- The positive critical loops of a level with a given prime image form a compact set. -/
theorem isCompact_posCrit_image (F : ReversibleMetric n) (c : ℝ) (s : Set (Sphere n)) :
    IsCompact {γ : SphereLoop n | ∃ (hs : s ∈ primeImages F) (k : ℕ) (θ : Circ), 0 < k ∧
      (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c ∧
      γ = θ +ᵥ ofSmooth (iterate (chosen F s hs).loop k)} := by
  by_cases h : ∃ (hs : s ∈ primeImages F) (k : ℕ), 0 < k ∧
      (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c
  · obtain ⟨hs, k₀, hk₀, hc₀⟩ := h
    have heq : {γ : SphereLoop n | ∃ (hs : s ∈ primeImages F) (k : ℕ) (θ : Circ), 0 < k ∧
        (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c ∧
        γ = θ +ᵥ ofSmooth (iterate (chosen F s hs).loop k)} =
        range (fun θ : Circ => θ +ᵥ ofSmooth (iterate (chosen F s hs).loop k₀)) := by
      ext γ
      constructor
      · rintro ⟨hs', k, θ, -, hck, rfl⟩
        have hk : k = k₀ := by
          have h1 : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) =
              (k₀ : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) :=
            hck.trans hc₀.symm
          exact Nat.cast_injective (mul_right_cancel₀ (chosen_energy_pos F s hs).ne' h1)
        rw [hk]
        exact ⟨θ, rfl⟩
      · rintro ⟨θ, rfl⟩
        exact ⟨hs, k₀, θ, hk₀, hc₀, rfl⟩
    rw [heq]
    exact isCompact_orbit _
  · have heq : {γ : SphereLoop n | ∃ (hs : s ∈ primeImages F) (k : ℕ) (θ : Circ), 0 < k ∧
        (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c ∧
        γ = θ +ᵥ ofSmooth (iterate (chosen F s hs).loop k)} = ∅ := by
      ext γ
      constructor
      · rintro ⟨hs, k, θ, hk, hck, -⟩
        exact h ⟨hs, k, hk, hck⟩
      · intro hγ
        exact absurd hγ (notMem_empty γ)
    rw [heq]
    exact isCompact_empty

/-- With finitely many prime closed geodesic images the positive critical loops of a level
form a compact set. -/
theorem isCompact_posCrit (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (c : ℝ) :
    IsCompact (posCrit F c) := by
  have heq : posCrit F c = ⋃ s ∈ primeImages F,
      {γ : SphereLoop n | ∃ (hs : s ∈ primeImages F) (k : ℕ) (θ : Circ), 0 < k ∧
        (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c ∧
        γ = θ +ᵥ ofSmooth (iterate (chosen F s hs).loop k)} := by
    ext γ
    constructor
    · rintro ⟨s, hs, k, θ, hk, hck, rfl⟩
      exact mem_iUnion₂.mpr ⟨s, hs, hs, k, θ, hk, hck, rfl⟩
    · intro hγ
      obtain ⟨s, -, hs, k, θ, hk, hck, rfl⟩ := mem_iUnion₂.mp hγ
      exact ⟨s, hs, k, θ, hk, hck, rfl⟩
  rw [heq]
  exact hfin.isCompact_biUnion fun s _ => isCompact_posCrit_image F c s

theorem isCompact_negCrit (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (c : ℝ) :
    IsCompact (negCrit F c) :=
  (isCompact_posCrit F hfin c).image (reverseSphere_continuous n)

/-- A positive critical loop is not a negative critical loop. -/
theorem posCrit_inter_negCrit (F : ReversibleMetric n) (c : ℝ) (γ : SphereLoop n)
    (hp : γ ∈ posCrit F c) (hm : γ ∈ negCrit F c) : False := by
  obtain ⟨s, hs, k, θ, hk, hck, rfl⟩ := hp
  obtain ⟨_, ⟨s', hs', k', θ', hk', hck', rfl⟩, heq⟩ := hm
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨a', rfl⟩ := QuotientAddGroup.mk_surjective θ'
  have h1 : ofSmooth (reverse (shift (iterate (chosen F s' hs').loop k') a')) =
      ofSmooth (shift (iterate (chosen F s hs).loop k) a) := by
    rw [← reverseSphere_ofSmooth, ofSmooth_shift, ofSmooth_shift]
    exact heq
  have h2 := ofSmooth_injective h1
  have himg : s' = s := by
    have e := congrArg Finsler.Loops.image h2
    rw [image_reverse, image_shift, image_iterate _ (Nat.ne_of_gt hk'), image_shift,
      image_iterate _ (Nat.ne_of_gt hk), chosen_image, chosen_image] at e
    exact e
  subst himg
  have hkk : k' = k := by
    have h3 : (k' : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s' hs).loop) =
        (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s' hs).loop) :=
      hck'.trans hck.symm
    exact Nat.cast_injective (mul_right_cancel₀ (chosen_energy_pos F s' hs).ne' h3)
  subst hkk
  have h4 : reverse (shift (iterate (chosen F s' hs).loop k') a') =
      shift (shift (iterate (chosen F s' hs).loop k') a') (a - a') := by
    rw [shift_shift, sub_add_cancel]
    exact h2
  exact reverse_ne_shift_of_deriv (a - a')
    (deriv_shift_iterate_ne_zero (chosen F s' hs).regular (Nat.ne_of_gt hk') a' _) h4

/-! ### Uniform neighbourhoods -/

/-- The uniform distance of two loops is at most r if their representatives are within r on
the unit interval. -/
theorem dist_sphereCircleMap_le {r : ℝ} (hr : 0 ≤ r) (x y : SphereLoop n)
    (h : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ‖continuousRepresentative (x.data : Space n) t -
        continuousRepresentative (y.data : Space n) t‖ ≤ r) :
    dist (sphereCircleMap x) (sphereCircleMap y) ≤ r := by
  rw [ContinuousMap.dist_le hr]
  intro θ
  rw [sphereCircleMap_point, sphereCircleMap_point, Subtype.dist_eq, dist_eq_norm]
  exact h _ (circlePoint θ).2

/-- Reversal does not increase the uniform distance. -/
theorem dist_sphereCircleMap_reverse_le (x y : SphereLoop n) :
    dist (sphereCircleMap (reverseSphere x)) (sphereCircleMap (reverseSphere y)) ≤
      dist (sphereCircleMap x) (sphereCircleMap y) := by
  rw [ContinuousMap.dist_le dist_nonneg]
  intro θ
  rw [sphereCircleMap_point, sphereCircleMap_point, sphereRepresentative_reverseSphere,
    sphereRepresentative_reverseSphere, ← sphereCircleMap_coe, ← sphereCircleMap_coe]
  exact ContinuousMap.dist_apply_le_dist _

/-- The loops whose circle map is within r of that of a loop of a given set form an open
set. -/
theorem isOpen_near (C : Set (SphereLoop n)) (r : ℝ) :
    IsOpen {x : Loops n | ∃ γ ∈ C,
      dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ) < r} := by
  have h : {x : Loops n | ∃ γ ∈ C,
      dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ) < r} =
      ⋃ γ ∈ C, (fun x : Loops n => sphereCircleMap (x : SphereLoop n)) ⁻¹'
        Metric.ball (sphereCircleMap γ) r := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, Metric.mem_ball, exists_prop]
  rw [h]
  exact isOpen_biUnion fun γ _ => Metric.isOpen_ball.preimage (sphereCircleMap_continuous n)

/-- The loops uniformly within ρ of a tangent critical loop of energy c². -/
def tube (F : ReversibleMetric n) (c ρ : ℝ) : Set (Loops n) :=
  {x | ∃ γ : SphereLoop n, TangentCritical F γ ∧ energy F γ = c ^ 2 ∧
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ‖continuousRepresentative ((x : SphereLoop n).data : Space n) t -
        continuousRepresentative (γ.data : Space n) t‖ ≤ ρ}

/-- Separation: with finitely many prime closed geodesic images, positive and negative critical
loops of a level have uniform distance bounded below. -/
theorem exists_separation (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ₁ ∈ posCrit F c, ∀ γ₂ ∈ negCrit F c,
      δ ≤ dist (sphereCircleMap γ₁) (sphereCircleMap γ₂) := by
  have hK₁ : IsCompact (sphereCircleMap '' posCrit F c) :=
    (isCompact_posCrit F hfin c).image (sphereCircleMap_continuous n)
  have hK₂ : IsCompact (sphereCircleMap '' negCrit F c) :=
    (isCompact_negCrit F hfin c).image (sphereCircleMap_continuous n)
  by_cases hne₁ : (sphereCircleMap '' posCrit F c).Nonempty
  · by_cases hne₂ : (sphereCircleMap '' negCrit F c).Nonempty
    · obtain ⟨f₀, hf₀, hmin⟩ := hK₁.exists_isMinOn hne₁
        (Metric.continuous_infDist_pt (sphereCircleMap '' negCrit F c)).continuousOn
      have hnot : f₀ ∉ sphereCircleMap '' negCrit F c := by
        rintro ⟨γ₂, hγ₂, hγ₂f⟩
        obtain ⟨γ₁, hγ₁, hγ₁f⟩ := hf₀
        have he : γ₁ = γ₂ := sphereCircleMap_injective n (hγ₁f.trans hγ₂f.symm)
        exact posCrit_inter_negCrit F c γ₁ hγ₁ (he ▸ hγ₂)
      have hpos : 0 < Metric.infDist f₀ (sphereCircleMap '' negCrit F c) :=
        (hK₂.isClosed.notMem_iff_infDist_pos hne₂).mp hnot
      refine ⟨_, hpos, fun γ₁ hγ₁ γ₂ hγ₂ => ?_⟩
      exact (hmin ⟨γ₁, hγ₁, rfl⟩).trans
        (Metric.infDist_le_dist_of_mem ⟨γ₂, hγ₂, rfl⟩)
    · refine ⟨1, one_pos, fun γ₁ _ γ₂ hγ₂ => ?_⟩
      exact absurd ⟨_, γ₂, hγ₂, rfl⟩ hne₂
  · refine ⟨1, one_pos, fun γ₁ hγ₁ γ₂ _ => ?_⟩
    exact absurd ⟨_, γ₁, hγ₁, rfl⟩ hne₁

/-- The orientation of a uniform neighbourhood of the critical set of a level from a
separation constant. -/
def orientation (F : ReversibleMetric n) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hsep : ∀ γ₁ ∈ posCrit F c, ∀ γ₂ ∈ negCrit F c,
      δ ≤ dist (sphereCircleMap γ₁) (sphereCircleMap γ₂)) :
    Orientation (tube F c (δ / 4)) where
  pos := {x : Loops n | ∃ γ ∈ posCrit F c,
    dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ) < δ / 2}
  neg := {x : Loops n | ∃ γ ∈ negCrit F c,
    dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ) < δ / 2}
  pos_open := isOpen_near (posCrit F c) (δ / 2)
  neg_open := isOpen_near (negCrit F c) (δ / 2)
  cover := by
    rintro x ⟨γ, hγ, hE, hclose⟩
    have hd : dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ) < δ / 2 :=
      lt_of_le_of_lt (dist_sphereCircleMap_le (by positivity) _ _ hclose) (by linarith)
    rcases mem_posCrit_or_negCrit F hc γ hγ hE with h | h
    · exact Or.inl ⟨γ, h, hd⟩
    · exact Or.inr ⟨γ, h, hd⟩
  disjoint := by
    rintro x - ⟨γ₁, hγ₁, hd₁⟩ ⟨γ₂, hγ₂, hd₂⟩
    have h := hsep γ₁ hγ₁ γ₂ hγ₂
    have htri : dist (sphereCircleMap γ₁) (sphereCircleMap γ₂) ≤
        dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ₁) +
          dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ₂) :=
      dist_triangle_left _ _ _
    linarith
  rev_pos := by
    rintro u ⟨γ, hγ, hd⟩
    exact ⟨reverseSphere γ, ⟨γ, hγ, rfl⟩,
      lt_of_le_of_lt (dist_sphereCircleMap_reverse_le u γ) hd⟩
  rev_neg := by
    rintro u ⟨_, ⟨γ, hγ, rfl⟩, hd⟩
    refine ⟨γ, hγ, ?_⟩
    have h := dist_sphereCircleMap_reverse_le u (reverseSphere γ)
    rw [reverseSphere_involutive] at h
    exact lt_of_le_of_lt h hd

/-- With finitely many prime closed geodesic images, a uniform neighbourhood of the critical
set of a positive level is oriented. -/
theorem exists_orientation (F : ReversibleMetric n) (hfin : (primeImages F).Finite) {c : ℝ}
    (hc : 0 < c) : ∃ ρ : ℝ, 0 < ρ ∧ Nonempty (Orientation (tube F c ρ)) := by
  obtain ⟨δ, hδ, hsep⟩ := exists_separation F hfin c
  exact ⟨δ / 4, by positivity, ⟨orientation F hc hδ hsep⟩⟩

end

end Finsler.OrientedCritical
