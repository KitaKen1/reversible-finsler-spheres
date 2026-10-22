module

public import Finsler.Geometry.CircleEvenFields
public import Finsler.Geometry.LabelRotation
public import Finsler.Geometry.RootFieldRotation
public import Finsler.Analysis.InvariantCutoff

/-! The actual signed frame fields give invertible label charts and half-rotation naturality
on their common neighbourhood. The root field and cutoff must satisfy their stated invariance. -/

@[expose] public section

namespace Finsler.CircleLabelFields

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientSymmetry Finsler.AmbientNormalIndex Finsler.NormalFamily
open Finsler.CircleFrameField
open Finsler.SymmetricBlocks Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.RotationNatural Finsler.CircleHalfRotation Finsler.CurveEquivFrames
open Finsler.LabelAmbient Finsler.AmbientSplitField

noncomputable section
set_option maxSynthPendingDepth 5

variable {n : ℕ} {F : ReversibleMetric n} {g : Finsler.Geodesics.ClosedGeodesic F}
  {s m N b p : ℕ} [NeZero s] [NeZero m] [NeZero N]

/-- The field record supplies the pointwise signed frame law used by the label coordinates. -/
theorem field_equivariant {ε : ℝ} (G : SignedFrameField g s m N ε b)
    (z : ZMod (s * (2 * N)) → Ambient n) (i : Fin b) :
    G.G (rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z) i =
      G.d i • rotV m (s * (2 * N)) (halfIndex m s N) (G.G z i) :=
  congrArg (fun H => H i) (G.equivariant z)

variable (G₁ : SignedFrameField g s m N 1 b) (G₂ : SignedFrameField g s m N (-1) p)
  (ψ : normal (rotL (n := n) m (s * (2 * N))) m ≃L[ℝ]
    (Fin b → ℝ) × (Fin p → ℝ))

/-- Maximal opposite definite frames make the actual chart invertible on the common set. -/
theorem isUnit_on {z : ZMod (s * (2 * N)) → Ambient n} (hz : z ∈ G₁.U ∩ G₂.U) :
    IsUnit (matA m (s * (2 * N)) G₁.G G₂.G ψ z) := by
  apply isUnit_matA m (s * (2 * N)) G₁.G G₂.G ψ
    (β := normalForm m (s * (2 * N)) F z)
  · simpa only [one_smul] using G₁.definite z hz.1
  · simpa only [neg_one_smul] using G₂.definite z hz.2

/-- The actual split field is half-rotation equivariant wherever both adapted fields are definite. -/
theorem splitW_half
    (V₀ : (ZMod (s * (2 * N)) → Ambient n) → ZMod (s * (2 * N)) → Ambient n)
    (hV₀ : ∀ z, V₀ (rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z) =
      rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) (V₀ z))
    {Q : ZMod (m * (s * (2 * N))) → Ambient n}
    (hQ : zOf m (s * (2 * N)) Q ∈ G₁.U ∩ G₂.U) :
    splitW m (s * (2 * N)) G₁.G G₂.G ψ V₀
        (rotA (m * (s * (2 * N))) (halfIndex m s N) Q) =
      rotA (m * (s * (2 * N))) (halfIndex m s N)
        (splitW m (s * (2 * N)) G₁.G G₂.G ψ V₀ Q) := by
  apply splitW_rotA m (s * (2 * N)) G₁.G G₂.G ψ V₀ (halfIndex m s N) G₁.d G₂.d
    G₁.signs G₂.signs G₁.smooth G₂.smooth (field_equivariant G₁) (field_equivariant G₂) hV₀
    (isUnit_on G₁ G₂ ψ hQ)
  exact isUnit_on G₁ G₂ ψ ⟨(G₁.invariant _).mpr hQ.1, (G₂.invariant _).mpr hQ.2⟩

/-- An invariant root cutoff gives an invariant actual label function on the common chart. -/
theorem gDef_half (χ₀ : (ZMod (s * (2 * N)) → Ambient n) → ℝ)
    (hχ : ∀ z, χ₀ (rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z) = χ₀ z)
    (r lam : ℝ) {Q : ZMod (m * (s * (2 * N))) → Ambient n}
    (hQ : zOf m (s * (2 * N)) Q ∈ G₁.U ∩ G₂.U) :
    gDef m (s * (2 * N)) F G₁.G G₂.G ψ χ₀ r lam
        (rotA (m * (s * (2 * N))) (halfIndex m s N) Q) =
      gDef m (s * (2 * N)) F G₁.G G₂.G ψ χ₀ r lam Q := by
  exact Finsler.LabelRotation.gDef_rotA m (s * (2 * N)) F G₁.G G₂.G
    (halfIndex m s N) G₁.d G₂.d G₁.signs G₂.signs (field_equivariant G₁)
    (field_equivariant G₂) ψ (isUnit_on G₁ G₂ ψ hQ)
    (isUnit_on G₁ G₂ ψ ⟨(G₁.invariant _).mpr hQ.1, (G₂.invariant _).mpr hQ.2⟩) χ₀ hχ r lam

end

end Finsler.CircleLabelFields
