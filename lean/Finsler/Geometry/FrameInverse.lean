module

public import Finsler.Geometry.FrameCoordinates

/-! The inverse of the frame coordinates. The ambient polygons with m N vertices split into the
iterated polygons and the normal space; the projection onto the iterated polygons along the
normal space is (1/m) times the sum of the powers of the rotation by one period, and the root
polygon of an ambient polygon is the restriction of its projection. Composing the fibre part of
the frame coordinates at z with the complementary projection and a fixed linear isomorphism of
the normal space with the coefficient space gives a linear endomorphism A(z) of the coefficient
space; if G₁(z) is a negative and G₂(z) a positive frame for a symmetric bilinear function on
the normal space, the combined frame is linearly independent and A(z) is invertible. Then the
frame coordinates are inverted explicitly: the root polygon is the restricted projection, and
the coefficients are A(z)⁻¹ applied to the coordinates of the normal part. The inverse is
smooth where A is invertible, since inversion is smooth at the units of a complete normed ring.
No inverse function theorem is used. -/

@[expose] public section

namespace Finsler.FrameInverse

open Module Filter Set
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

/-! ### The projection onto the iterated polygons -/

/-- The projection onto the iterated polygons along the normal space. -/
def projZ : (ZMod (m * N) → Ambient n) →L[ℝ] (ZMod (m * N) → Ambient n) :=
  ((m : ℝ)⁻¹) • LinearMap.toContinuousLinearMap (powSum (rotL (n := n) m N) m)

theorem projZ_apply (Q : ZMod (m * N) → Ambient n) :
    projZ m N Q = ((m : ℝ)⁻¹) • powSum (rotL (n := n) m N) m Q := rfl

theorem projZ_iterA (z : ZMod N → Ambient n) : projZ m N (iterA m N z) = iterA m N z := by
  have hfix : rotL (n := n) m N (iterA m N z) = iterA m N z := rotA_iterate m N z
  rw [projZ_apply, powSum_fixed _ _ hfix, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m)), one_smul]

theorem projZ_normal {w : ZMod (m * N) → Ambient n} (hw : w ∈ normal (rotL (n := n) m N) m) :
    projZ m N w = 0 := by
  rw [projZ_apply, (mem_normal _ _ w).mp hw, smul_zero]

theorem projZ_mem_fixed (Q : ZMod (m * N) → Ambient n) :
    projZ m N Q ∈ fixed (rotL (n := n) m N) := by
  rw [mem_fixed, projZ_apply, map_smul, map_powSum (rotL_pow m N)]

theorem sub_projZ_mem_normal (Q : ZMod (m * N) → Ambient n) :
    Q - projZ m N Q ∈ normal (rotL (n := n) m N) m := by
  rw [mem_normal, map_sub, projZ_apply, map_smul,
    powSum_fixed _ _ (map_powSum (rotL_pow (n := n) m N) Q), smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m)), one_smul, sub_self]

/-- The root polygon of an ambient polygon. -/
def zOf : (ZMod (m * N) → Ambient n) →L[ℝ] (ZMod N → Ambient n) :=
  (resA (n := n) m N).comp (projZ m N)

theorem iterA_zOf (Q : ZMod (m * N) → Ambient n) : iterA m N (zOf m N Q) = projZ m N Q := by
  have h := projZ_mem_fixed m N Q
  rw [fixed_rotL] at h
  obtain ⟨y, hy⟩ := h
  change iterA m N (resA m N (projZ m N Q)) = projZ m N Q
  rw [← hy]
  change iterA m N (resA m N (iterA m N y)) = iterA m N y
  rw [resA_iterA]

theorem zOf_iterA_add {z : ZMod N → Ambient n} {w : ZMod (m * N) → Ambient n}
    (hw : w ∈ normal (rotL (n := n) m N) m) : zOf m N (iterA m N z + w) = z := by
  change resA m N (projZ m N (iterA m N z + w)) = z
  rw [map_add, projZ_iterA, projZ_normal m N hw, add_zero, resA_iterA]

/-- The projection onto the normal space along the iterated polygons. -/
def projV : (ZMod (m * N) → Ambient n) →L[ℝ] normal (rotL (n := n) m N) m :=
  (ContinuousLinearMap.id ℝ (ZMod (m * N) → Ambient n) - projZ m N).codRestrict
    (normal (rotL (n := n) m N) m) fun Q => sub_projZ_mem_normal m N Q

theorem projV_coe (Q : ZMod (m * N) → Ambient n) :
    ((projV m N Q : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) =
      Q - projZ m N Q := rfl

theorem projV_normal {w : ZMod (m * N) → Ambient n} (hw : w ∈ normal (rotL (n := n) m N) m) :
    ((projV m N w : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) = w := by
  rw [projV_coe, projZ_normal m N hw, sub_zero]

/-- Every ambient polygon is the iterate of its root polygon plus its normal part. -/
theorem iterA_zOf_add_projV (Q : ZMod (m * N) → Ambient n) :
    iterA m N (zOf m N Q) + ((projV m N Q : normal (rotL (n := n) m N) m) :
      ZMod (m * N) → Ambient n) = Q := by
  rw [iterA_zOf, projV_coe, add_sub_cancel]

/-! ### Linear independence of a negative and a positive frame -/

section Independent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {b p : ℕ}

/-- A negative and a positive frame together are linearly independent: a vanishing combination
has vanishing negative and positive parts. -/
theorem eq_zero_of_comb_add {β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {G₁ : Fin b → V} {G₂ : Fin p → V}
    (h₁ : Neg β G₁) (h₂ : Neg (-β) G₂) {x : Fin b → ℝ} {y : Fin p → ℝ}
    (h : comb G₁ x + comb G₂ y = 0) : x = 0 ∧ y = 0 := by
  have hc : comb G₁ x = -comb G₂ y := eq_neg_of_add_eq_zero_left h
  have hval : β (comb G₁ x) (comb G₁ x) = β (comb G₂ y) (comb G₂ y) := by
    simp only [hc, map_neg, LinearMap.neg_apply, neg_neg]
  by_contra hne
  rcases not_and_or.mp hne with hx | hy
  · have h1 := h₁ x hx
    by_cases hy : y = 0
    · have h0 : comb G₂ y = 0 := by rw [hy]; simp [comb]
      rw [hval, h0, map_zero] at h1
      exact lt_irrefl _ h1
    · have h2 := h₂ y hy
      change 0 > -(β (comb G₂ y) (comb G₂ y)) at h2
      linarith
  · have h2 := h₂ y hy
    change 0 > -(β (comb G₂ y) (comb G₂ y)) at h2
    by_cases hx : x = 0
    · have h0 : comb G₁ x = 0 := by rw [hx]; simp [comb]
      rw [← hval, h0, map_zero] at h2
      simp at h2
    · have h1 := h₁ x hx
      linarith

end Independent

/-! ### The inverse of the frame coordinates -/

section Inverse

variable {b p : ℕ} (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))

/-- The coefficient map of the frames at z, composed with the coordinates of the normal
space. -/
def matA (z : ZMod N → Ambient n) :
    ((Fin b → ℝ) × (Fin p → ℝ)) →L[ℝ] ((Fin b → ℝ) × (Fin p → ℝ)) :=
  ((ψ : normal (rotL (n := n) m N) m →L[ℝ] (Fin b → ℝ) × (Fin p → ℝ)).comp (projV m N)).comp
    (fibreL m N G₁ G₂ z)

theorem matA_apply (z : ZMod N → Ambient n) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    matA m N G₁ G₂ ψ z ξ = ψ ⟨fibreL m N G₁ G₂ z ξ, fibreL_mem m N G₁ G₂ z ξ⟩ := by
  change ψ (projV m N (fibreL m N G₁ G₂ z ξ)) = _
  congr 1
  exact Subtype.ext (projV_normal m N (fibreL_mem m N G₁ G₂ z ξ))

/-- The coefficient map is invertible where the frames are a negative and a positive frame. -/
theorem isUnit_matA {β : normal (rotL (n := n) m N) m →ₗ[ℝ] normal (rotL (n := n) m N) m →ₗ[ℝ] ℝ}
    {z : ZMod N → Ambient n} (h₁ : Neg β (G₁ z)) (h₂ : Neg (-β) (G₂ z)) :
    IsUnit (matA m N G₁ G₂ ψ z) := by
  have hinj : Function.Injective (matA m N G₁ G₂ ψ z) := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    rw [matA_apply] at hξ
    have h1 : (⟨fibreL m N G₁ G₂ z ξ, fibreL_mem m N G₁ G₂ z ξ⟩ :
        normal (rotL (n := n) m N) m) = 0 := ψ.injective (hξ.trans (map_zero ψ).symm)
    have h2 : comb (G₁ z) ξ.1 + comb (G₂ z) ξ.2 = 0 := by
      apply Subtype.ext
      have h3 := congrArg Subtype.val h1
      rw [Submodule.coe_add]
      rw [← fibreL_apply m N G₁ G₂ z ξ]
      exact h3
    obtain ⟨hx, hy⟩ := eq_zero_of_comb_add h₁ h₂ h2
    exact Prod.ext hx hy
  have hsurj : Function.Surjective (matA m N G₁ G₂ ψ z) :=
    LinearMap.injective_iff_surjective.mp hinj
  let e : ((Fin b → ℝ) × (Fin p → ℝ)) ≃L[ℝ] ((Fin b → ℝ) × (Fin p → ℝ)) :=
    (LinearEquiv.ofBijective (matA m N G₁ G₂ ψ z).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨(ContinuousLinearEquiv.unitsEquiv ℝ _).symm e, rfl⟩

/-- The coefficients of an ambient polygon in the frame coordinates. -/
def xiOf (Q : ZMod (m * N) → Ambient n) : (Fin b → ℝ) × (Fin p → ℝ) :=
  Ring.inverse (matA m N G₁ G₂ ψ (zOf m N Q)) (ψ (projV m N Q))

/-- **Inverse of the frame coordinates (first half).** -/
theorem inverse_coord {z : ZMod N → Ambient n} (hz : IsUnit (matA m N G₁ G₂ ψ z))
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    zOf m N (coord m N G₁ G₂ (z, ξ)) = z ∧ xiOf m N G₁ G₂ ψ (coord m N G₁ G₂ (z, ξ)) = ξ := by
  have hz' : zOf m N (coord m N G₁ G₂ (z, ξ)) = z :=
    zOf_iterA_add m N (fibreL_mem m N G₁ G₂ z ξ)
  refine ⟨hz', ?_⟩
  unfold xiOf
  rw [hz']
  have hV : projV m N (coord m N G₁ G₂ (z, ξ)) =
      ⟨fibreL m N G₁ G₂ z ξ, fibreL_mem m N G₁ G₂ z ξ⟩ := by
    apply Subtype.ext
    rw [projV_coe]
    change iterA m N z + fibreL m N G₁ G₂ z ξ - projZ m N (iterA m N z + fibreL m N G₁ G₂ z ξ) =
      fibreL m N G₁ G₂ z ξ
    rw [map_add, projZ_iterA, projZ_normal m N (fibreL_mem m N G₁ G₂ z ξ), add_zero,
      add_sub_cancel_left]
  rw [hV, ← matA_apply]
  obtain ⟨u, hu⟩ := hz
  rw [← hu, Ring.inverse_unit]
  exact congrArg (fun f : ((Fin b → ℝ) × (Fin p → ℝ)) →L[ℝ] ((Fin b → ℝ) × (Fin p → ℝ)) => f ξ)
    (Units.inv_mul u)

/-- **Inverse of the frame coordinates (second half).** -/
theorem coord_inverse {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))) :
    coord m N G₁ G₂ (zOf m N Q, xiOf m N G₁ G₂ ψ Q) = Q := by
  have h1 : matA m N G₁ G₂ ψ (zOf m N Q) (xiOf m N G₁ G₂ ψ Q) = ψ (projV m N Q) := by
    unfold xiOf
    obtain ⟨u, hu⟩ := hQ
    rw [← hu, Ring.inverse_unit]
    exact congrArg (fun f : ((Fin b → ℝ) × (Fin p → ℝ)) →L[ℝ] ((Fin b → ℝ) × (Fin p → ℝ)) =>
      f (ψ (projV m N Q))) (Units.mul_inv u)
  rw [matA_apply] at h1
  have h2 := congrArg Subtype.val (ψ.injective h1)
  change fibreL m N G₁ G₂ (zOf m N Q) (xiOf m N G₁ G₂ ψ Q) =
    ((projV m N Q : normal (rotL (n := n) m N) m) : ZMod (m * N) → Ambient n) at h2
  unfold coord
  rw [h2]
  exact iterA_zOf_add_projV m N Q

/-- The coefficient map depends smoothly on the root polygon. -/
theorem matA_contDiff (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂) :
    ContDiff ℝ ∞ (matA m N G₁ G₂ ψ) := by
  have hfib : ContDiff ℝ ∞ (fun z => fibreL m N G₁ G₂ z) := by
    have h : (fun z => fibreL m N G₁ G₂ z) = fun z =>
        (∑ i, ContinuousLinearMap.smulRightL ℝ ((Fin b → ℝ) × (Fin p → ℝ))
            (ZMod (m * N) → Ambient n)
            ((ContinuousLinearMap.proj i).comp
              (ContinuousLinearMap.fst ℝ (Fin b → ℝ) (Fin p → ℝ)))
            ((normal (rotL (n := n) m N) m).subtypeL (G₁ z i))) +
        ∑ j, ContinuousLinearMap.smulRightL ℝ ((Fin b → ℝ) × (Fin p → ℝ))
            (ZMod (m * N) → Ambient n)
            ((ContinuousLinearMap.proj j).comp
              (ContinuousLinearMap.snd ℝ (Fin b → ℝ) (Fin p → ℝ)))
            ((normal (rotL (n := n) m N) m).subtypeL (G₂ z j)) := by
      funext z
      rfl
    rw [h]
    refine (ContDiff.sum fun i _ => ?_).add (ContDiff.sum fun j _ => ?_)
    · exact (ContinuousLinearMap.contDiff _).comp ((normal (rotL (n := n) m N) m).subtypeL.contDiff.comp
        ((contDiff_apply ℝ (normal (rotL (n := n) m N) m) i).comp hG₁))
    · exact (ContinuousLinearMap.contDiff _).comp ((normal (rotL (n := n) m N) m).subtypeL.contDiff.comp
        ((contDiff_apply ℝ (normal (rotL (n := n) m N) m) j).comp hG₂))
  have h : matA m N G₁ G₂ ψ = fun z =>
      ContinuousLinearMap.compL ℝ ((Fin b → ℝ) × (Fin p → ℝ)) (ZMod (m * N) → Ambient n)
        ((Fin b → ℝ) × (Fin p → ℝ))
        ((ψ : normal (rotL (n := n) m N) m →L[ℝ] (Fin b → ℝ) × (Fin p → ℝ)).comp (projV m N))
        (fibreL m N G₁ G₂ z) := by
    funext z
    rfl
  rw [h]
  exact (ContinuousLinearMap.contDiff _).comp hfib

/-- The coefficients are smooth where the coefficient map of the root polygon is invertible. -/
theorem xiOf_contDiffAt (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))) :
    ContDiffAt ℝ ∞ (xiOf m N G₁ G₂ ψ) Q := by
  obtain ⟨u, hu⟩ := hQ
  have hinv : ContDiffAt ℝ ∞ (Ring.inverse :
      (((Fin b → ℝ) × (Fin p → ℝ)) →L[ℝ] ((Fin b → ℝ) × (Fin p → ℝ))) →
        (((Fin b → ℝ) × (Fin p → ℝ)) →L[ℝ] ((Fin b → ℝ) × (Fin p → ℝ))))
      (matA m N G₁ G₂ ψ (zOf m N Q)) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have hA : ContDiffAt ℝ ∞ (fun Q => matA m N G₁ G₂ ψ (zOf m N Q)) Q :=
    ((matA_contDiff m N G₁ G₂ ψ hG₁ hG₂).comp (zOf (n := n) m N).contDiff).contDiffAt
  have hB : ContDiffAt ℝ ∞ (fun Q => Ring.inverse (matA m N G₁ G₂ ψ (zOf m N Q))) Q :=
    ContDiffAt.comp (g := Ring.inverse) (f := fun Q => matA m N G₁ G₂ ψ (zOf m N Q)) Q hinv hA
  have hC : ContDiffAt ℝ ∞ (fun Q => ψ (projV m N Q)) Q :=
    (((ψ : normal (rotL (n := n) m N) m →L[ℝ] (Fin b → ℝ) × (Fin p → ℝ)).comp
      (projV m N)).contDiff).contDiffAt
  exact hB.clm_apply hC

/-- The set of the ambient polygons whose root polygon has an invertible coefficient map is
open. -/
theorem isOpen_isUnit (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂) :
    IsOpen {Q : ZMod (m * N) → Ambient n | IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))} := by
  have hc : Continuous fun Q : ZMod (m * N) → Ambient n => matA m N G₁ G₂ ψ (zOf m N Q) :=
    (matA_contDiff m N G₁ G₂ ψ hG₁ hG₂).continuous.comp (zOf (n := n) m N).continuous
  exact Units.isOpen.preimage hc

end Inverse

end

end Finsler.FrameInverse
