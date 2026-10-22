module

public import Finsler.Loop.OriginalFirstHalfJointCochains

/-! The actual zero-rotation near-pair cylinder cover and its
proper cut rectangles, before inserting the spatial join cochain. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)

abbrev space : TopCat.{0} := TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)

def source : TopCat.of (FirstInputRotatingCut.source α β R r) ⟶ space α β R :=
  SupportedCap.subspaceMap (space α β R) (FirstInputRotatingCut.source α β R r)

theorem source_square : source α β R r ≫ rotatingZero α β R =
    FirstInputRotationEndpoints.stage α β R r 0 ≫ FirstInputRotationAmbientCover.source α β R r :=
  OriginalFirstHalfJointCochains.rotating_square α β R r

def cover (η ρ : ℝ) (i : Option (FirstInputRotationCochains.space α β R r)) : Set (space α β R) :=
  rotatingZero α β R ⁻¹' FirstInputRotationAmbientCover.cover α β R r η ρ i

theorem cover_open (η ρ : ℝ) (i : Option (FirstInputRotationCochains.space α β R r)) :
    IsOpen (cover α β R r η ρ i) :=
  (FirstInputRotationAmbientCover.cover_open α β R r η ρ i).preimage (rotatingZero α β R).hom.continuous

theorem cover_univ {η ρ : ℝ} (hη : 0 < η) (hρr : ρ < r) :
    ⋃ i, cover α β R r η ρ i = Set.univ := by
  simp only [cover, ← Set.preimage_iUnion,
    FirstInputRotationAmbientCover.cover_univ α β R r η hη hρr, Set.preimage_univ]

theorem near_image (η ρ : ℝ) (i : FirstInputRotationCochains.space α β R r) :
    cover α β R r η ρ (some i) ⊆
      source α β R r '' FirstInputRotationEndpoints.cover α β R r η 0 i := by
  intro z hz
  have hz' : rotatingZero α β R z ∈ FirstInputRotationAmbientCover.cover α β R r η ρ (some i) := hz
  have hcut : z ∈ FirstInputRotatingCut.source α β R r := by
    exact (show FirstInputRotationAmbientCover.gap α β R (rotatingZero α β R z) < r from hz'.2).le
  let zP : FirstInputRotatingCut.source α β R r := ⟨z, hcut⟩
  obtain ⟨y, hy, hey⟩ := FirstInputRotationAmbientCover.near_image α β R r η ρ i hz'
  change (y.1, y.2.val) = (0, z) at hey
  have hyEq : y = FirstInputRotationEndpoints.stage α β R r 0 zP := by
    apply Prod.ext
    · exact congrArg (fun w : FirstInputRotationAmbientCover.ambient α β R => w.1) hey
    · apply Subtype.ext
      exact congrArg (fun w : FirstInputRotationAmbientCover.ambient α β R => w.2) hey
  refine ⟨zP, ?_, rfl⟩
  change FirstInputRotationEndpoints.stage α β R r 0 zP ∈ FirstInputRotationFilteredCap.rectangle α β R r η i
  rw [← hyEq]
  exact hy

end
end Finsler.OriginalFirstHalfZeroCover
