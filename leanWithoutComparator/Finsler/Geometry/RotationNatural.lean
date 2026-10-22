module

public import Finsler.Geometry.AmbientSplitField
public import Finsler.Geometry.AmbientRotation

/-! Rotation naturality of the explicit root and normal projections. The root of a rotated
ambient polygon is the rotated root, with the shift reduced modulo the number of root vertices.
This is proved from the explicit finite average, rather than a new decomposition theorem.
Frame-coordinate equivariance then follows by checking the frame combinations. -/

@[expose] public section

namespace Finsler.RotationNatural

open Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientSymmetry Finsler.AmbientNormalIndex Finsler.SymmetricBlocks
open Finsler.FrameCoordinates Finsler.FrameInverse Finsler.DefiniteFrames
open Finsler.NormalFamily
open scoped ContDiff

noncomputable section

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

omit [NeZero m] [NeZero N] in
/-- Iteration intertwines any rotation with the corresponding reduced rotation of the root. -/
theorem iterA_rotA (s : ZMod (m * N)) (z : ZMod N → Ambient n) :
    iterA m N (rotA N (red m N s) z) = rotA (m * N) s (iterA m N z) := by
  funext i
  change z (red m N i + red m N s) = z (red m N (i + s))
  rw [map_add]

omit [NeZero m] [NeZero N] in
/-- The finite orbit sum commutes with all vertex rotations. -/
theorem powSum_rotA (s : ZMod (m * N)) (Q : ZMod (m * N) → Ambient n) :
    powSum (rotL m N) m (rotA (m * N) s Q) =
      rotA (m * N) s (powSum (rotL m N) m Q) := by
  rw [powSum_apply, powSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact NormalFamily.rotL_pow_rotA m N s j Q

/-- The explicit projection onto the iterated polygons commutes with rotations. -/
theorem projZ_rotA (s : ZMod (m * N)) (Q : ZMod (m * N) → Ambient n) :
    projZ m N (rotA (m * N) s Q) = rotA (m * N) s (projZ m N Q) := by
  rw [projZ_apply, projZ_apply, map_smul, powSum_rotA]

/-- The root of a rotated polygon is the rotated root. -/
theorem zOf_rotA (s : ZMod (m * N)) (Q : ZMod (m * N) → Ambient n) :
    zOf m N (rotA (m * N) s Q) = rotA N (red m N s) (zOf m N Q) := by
  apply iterA_injective m N
  rw [iterA_zOf, iterA_rotA, iterA_zOf, projZ_rotA]

/-- The normal projection is natural under rotations. -/
theorem projV_rotA (s : ZMod (m * N)) (Q : ZMod (m * N) → Ambient n) :
    projV m N (rotA (m * N) s Q) = rotV m N s (projV m N Q) := by
  apply Subtype.ext
  rw [projV_coe, rotV_coe, projV_coe, map_sub, projZ_rotA]

omit [NeZero m] [NeZero N] in
/-- The restricted rotations compose additively. -/
theorem rotV_rotV (s t : ZMod (m * N)) (Q : normal (rotL (n := n) m N) m) :
    rotV m N s (rotV m N t Q) = rotV m N (s + t) Q := by
  apply Subtype.ext
  simp only [rotV_coe, rotA_rotA]

omit [NeZero m] [NeZero N] in
/-- The zero rotation on the normal space is the identity. -/
theorem rotV_zero (Q : normal (rotL (n := n) m N) m) : rotV m N 0 Q = Q := by
  apply Subtype.ext
  rw [rotV_coe, rotA_zero]

section Norm

variable (K : ℕ) [NeZero K]

/-- A vertex permutation does not increase the ambient product norm. -/
theorem norm_rotA_le (s : ZMod K) (Q : ZMod K → Ambient n) : ‖rotA K s Q‖ ≤ ‖Q‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg Q)).mpr fun i => norm_le_pi_norm Q (i + s)

/-- Rotations preserve the ambient product norm. -/
theorem norm_rotA (s : ZMod K) (Q : ZMod K → Ambient n) : ‖rotA K s Q‖ = ‖Q‖ := by
  apply le_antisymm (norm_rotA_le K s Q)
  have h := norm_rotA_le K (-s) (rotA K s Q)
  rwa [rotA_rotA, neg_add_cancel, rotA_zero] at h

end Norm

/-- The rotation on the normal subspace is an isometry for the inherited norm. -/
theorem norm_rotV (s : ZMod (m * N)) (Q : normal (rotL (n := n) m N) m) :
    ‖rotV m N s Q‖ = ‖Q‖ := by
  change ‖(rotV m N s Q : ZMod (m * N) → Ambient n)‖ =
    ‖(Q : ZMod (m * N) → Ambient n)‖
  rw [rotV_coe]
  exact norm_rotA (n := n) (m * N) s (Q : ZMod (m * N) → Ambient n)

section Frames

variable {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)

/-- A diagonal coefficient map. For adapted frames its entries are signs. -/
def diagonal (d : Fin b → ℝ) : (Fin b → ℝ) →L[ℝ] (Fin b → ℝ) :=
  ContinuousLinearMap.pi fun i => d i • ContinuousLinearMap.proj i

theorem diagonal_apply (d : Fin b → ℝ) (x : Fin b → ℝ) (i : Fin b) :
    diagonal d x i = d i * x i := rfl

/-- Diagonal changes of signs are involutions, with no parity assumption. -/
theorem diagonal_involutive (d : Fin b → ℝ) (hd : ∀ i, d i * d i = 1) (x : Fin b → ℝ) :
    diagonal d (diagonal d x) = x := by
  funext i
  rw [diagonal_apply, diagonal_apply, ← mul_assoc, hd, one_mul]

/-- Frame combinations transform by the same diagonal coefficient map. -/
theorem comb_rotV (s : ZMod (m * N)) (d : Fin b → ℝ) (z : ZMod N → Ambient n)
    (hG : ∀ i, G₁ (rotA N (red m N s) z) i = d i • rotV m N s (G₁ z i))
    (x : Fin b → ℝ) :
    comb (G₁ (rotA N (red m N s) z)) x = rotV m N s (comb (G₁ z) (diagonal d x)) := by
  simp only [comb, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hG, smul_smul, diagonal_apply, mul_comm (x i) (d i)]

/-- Coordinate equivariance is a direct consequence of the two frame identities. -/
theorem coord_rotA (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (z : ZMod N → Ambient n)
    (h₁ : ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    coord m N G₁ G₂ (rotA N (red m N s) z, ξ) =
      rotA (m * N) s (coord m N G₁ G₂ (z, (diagonal d₁ ξ.1, diagonal d₂ ξ.2))) := by
  simp only [coord, fibreL_apply, map_add, iterA_rotA]
  rw [comb_rotV m N G₁ s d₁ z h₁, comb_rotV m N G₂ s d₂ z h₂]
  rfl

/-- The hyperbolic coefficient field commutes with every block diagonal coefficient map. -/
theorem swapJ_diagonal (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    swapJ (diagonal d₁ ξ.1, diagonal d₂ ξ.2) =
      (diagonal d₁ (swapJ ξ).1, diagonal d₂ (swapJ ξ).2) := by
  apply Prod.ext
  · rfl
  · change -(diagonal d₂ ξ.2) = diagonal d₂ (-ξ.2)
    rw [map_neg]

/-- The coefficient action of the two diagonal sign maps. -/
def coeffD (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ) :
    ((Fin b → ℝ) × (Fin p → ℝ)) →L[ℝ] ((Fin b → ℝ) × (Fin p → ℝ)) :=
  (diagonal d₁).prodMap (diagonal d₂)

theorem coeffD_involutive (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : coeffD d₁ d₂ (coeffD d₁ d₂ ξ) = ξ :=
  Prod.ext (diagonal_involutive d₁ hd₁ ξ.1) (diagonal_involutive d₂ hd₂ ξ.2)

/-- The rotation action in root and frame coordinates. -/
def chartR (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ) :
    ((ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) →L[ℝ]
      ((ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :=
  (rotA N (red m N s)).prodMap (coeffD d₁ d₂)

/-- With sign matrices, the frame coordinates intertwine the two actions. -/
theorem coord_chartR (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (z : ZMod N → Ambient n)
    (h₁ : ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    coord m N G₁ G₂ (chartR m N s d₁ d₂ (z, ξ)) =
      rotA (m * N) s (coord m N G₁ G₂ (z, ξ)) := by
  change coord m N G₁ G₂ (rotA N (red m N s) z, coeffD d₁ d₂ ξ) = _
  rw [coord_rotA m N G₁ G₂ s d₁ d₂ z h₁ h₂]
  change rotA (m * N) s (coord m N G₁ G₂ (z, coeffD d₁ d₂ (coeffD d₁ d₂ ξ))) = _
  rw [coeffD_involutive d₁ d₂ hd₁ hd₂]

/-- Inverse-coordinate naturality follows from the known inverse, without differentiating
or transforming matrix inverses. Both frame charts must be invertible at the points used. -/
theorem xiOf_rotA
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    {Q : ZMod (m * N) → Ambient n}
    (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (hQ' : IsUnit (matA m N G₁ G₂ ψ (rotA N (red m N s) (zOf m N Q))))
    (h₁ : ∀ i, G₁ (rotA N (red m N s) (zOf m N Q)) i =
      d₁ i • rotV m N s (G₁ (zOf m N Q) i))
    (h₂ : ∀ i, G₂ (rotA N (red m N s) (zOf m N Q)) i =
      d₂ i • rotV m N s (G₂ (zOf m N Q) i)) :
    xiOf m N G₁ G₂ ψ (rotA (m * N) s Q) = coeffD d₁ d₂ (xiOf m N G₁ G₂ ψ Q) := by
  have hc := coord_chartR m N G₁ G₂ s d₁ d₂ hd₁ hd₂ (zOf m N Q) h₁ h₂
    (xiOf m N G₁ G₂ ψ Q)
  rw [coord_inverse m N G₁ G₂ ψ hQ] at hc
  have hi := (inverse_coord m N G₁ G₂ ψ hQ' (coeffD d₁ d₂ (xiOf m N G₁ G₂ ψ Q))).2
  change xiOf m N G₁ G₂ ψ (coord m N G₁ G₂
    (chartR m N s d₁ d₂ (zOf m N Q, xiOf m N G₁ G₂ ψ Q))) = _ at hi
  rwa [hc] at hi

/-- The coordinate derivative intertwines the actions by the chain rule. -/
theorem fderiv_coord_chartR (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (h₁ : ∀ z i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (q v : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :
    fderiv ℝ (coord m N G₁ G₂) (chartR m N s d₁ d₂ q) (chartR m N s d₁ d₂ v) =
      rotA (m * N) s (fderiv ℝ (coord m N G₁ G₂) q v) := by
  have hd := (coord_contDiff m N G₁ G₂ hG₁ hG₂).differentiable (by simp)
  have hl := (hd (chartR m N s d₁ d₂ q)).hasFDerivAt.comp q (chartR m N s d₁ d₂).hasFDerivAt
  have hr := (rotA (n := n) (m * N) s).hasFDerivAt.comp q (hd q).hasFDerivAt
  have he : coord m N G₁ G₂ ∘ chartR m N s d₁ d₂ =
      rotA (m * N) s ∘ coord m N G₁ G₂ :=
    funext fun w => coord_chartR m N G₁ G₂ s d₁ d₂ hd₁ hd₂ w.1 (h₁ w.1) (h₂ w.1) w.2
  have hder := hl.fderiv
  rw [he, hr.fderiv] at hder
  exact (congrArg (fun L => L v) hder).symm

/-- The ambient split field is equivariant whenever the root field and the two smooth
frames satisfy their stated transformation laws. Existence of such frames is separate. -/
theorem splitW_rotA
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (h₁ : ∀ z i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hV₀ : ∀ z, V₀ (rotA N (red m N s) z) = rotA N (red m N s) (V₀ z))
    {Q : ZMod (m * N) → Ambient n}
    (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (hQ' : IsUnit (matA m N G₁ G₂ ψ (rotA N (red m N s) (zOf m N Q)))) :
    Finsler.AmbientSplitField.splitW m N G₁ G₂ ψ V₀ (rotA (m * N) s Q) =
      rotA (m * N) s (Finsler.AmbientSplitField.splitW m N G₁ G₂ ψ V₀ Q) := by
  have hz := zOf_rotA m N s Q
  have hξ := xiOf_rotA m N G₁ G₂ ψ s d₁ d₂ hd₁ hd₂ hQ hQ' (h₁ _) (h₂ _)
  have h := fderiv_coord_chartR m N G₁ G₂ s d₁ d₂ hd₁ hd₂ hG₁ hG₂ h₁ h₂
    (zOf m N Q, xiOf m N G₁ G₂ ψ Q)
    (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q))
  have hdir : chartR m N s d₁ d₂
      (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q)) =
      (V₀ (rotA N (red m N s) (zOf m N Q)),
        swapJ (coeffD d₁ d₂ (xiOf m N G₁ G₂ ψ Q))) := by
    apply Prod.ext
    · exact (hV₀ _).symm
    · exact (swapJ_diagonal d₁ d₂ (xiOf m N G₁ G₂ ψ Q)).symm
  rw [hdir] at h
  simpa only [Finsler.AmbientSplitField.splitW, hz, hξ, chartR,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply] using h

end Frames

end

end Finsler.RotationNatural
