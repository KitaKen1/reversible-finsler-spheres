module

public import Finsler.Loop.SmallHomotopyCover
public import Finsler.Loop.OriginalFirstHalfJoinTimeCover
public import Finsler.Loop.CompactJoinCapLocalization
public import Finsler.Topology.TimePrismNaturality

/-! The spatial join cover pulled back to the entire actual annular
time cylinder, with its genuine small prism and near-cylinder source. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfAnnularJoinCover

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (κ : ℝ)

theorem spatial_square : (AnnularTimeTrim.cylinder (TopCat.of (P × Q))).h ≫ spatial α β =
    CartesianMonoidalCategory.fst (TopCat.of (P × Q)) TopCat.I := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def cover : (P × Q) → Set (ambient α β) :=
  SmallHomotopyCover.cover (spatial α β) (CompactJoinCapLocalization.cover α β κ)

theorem cover_open (i : P × Q) : IsOpen (cover α β κ i) :=
  SmallHomotopyCover.cover_open _ _ (CompactJoinCapLocalization.cover_open α β κ) i

theorem cover_univ (hκ : 0 < κ) : ⋃ i, cover α β κ i = Set.univ :=
  SmallHomotopyCover.cover_univ _ _ (CompactJoinCapLocalization.cover_univ α β hκ)

def prism (q : ℕ) :
    (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X q ⟶
      (small (ambient α β) (cover α β κ)).X (q + 1) :=
  SmallHomotopyCover.prism (AnnularTimeTrim.cylinder (TopCat.of (P × Q)))
    (spatial α β) (spatial_square α β) (CompactJoinCapLocalization.cover α β κ) q

theorem prism_inclusion (q : ℕ) :
    (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f q ≫
      AnnularTimeTrim.prism (TopCat.of (P × Q)) q =
    prism α β κ q ≫ (inclusion (ambient α β) (cover α β κ)).f (q + 1) :=
  SmallHomotopyCover.prism_inclusion (AnnularTimeTrim.cylinder (TopCat.of (P × Q)))
    (spatial α β) (spatial_square α β) (CompactJoinCapLocalization.cover α β κ) q

theorem nearSource_mono (R : ℝ) (q : ℕ) : Mono ((push (nearSource α β R)).f q) := by
  haveI : Mono (nearSource α β R) := (TopCat.mono_iff_injective _).mpr (by
    intro x y h
    apply Prod.ext
    · exact congrArg (fun z : ambient α β => z.1) h
    · apply Subtype.ext
      exact congrArg (fun z : ambient α β => z.2) h)
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (nearSource α β R)).app (Opposite.op ⦋q⦌))))

theorem near_prism_source (R : ℝ) (q : ℕ) :
    AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) q ≫
      (push (nearSource α β R)).f (q + 1) =
    (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f q ≫
      AnnularTimeTrim.prism (TopCat.of (P × Q)) q := by
  let X : TopCat.{0} := TopCat.of (CompactNearJoinParameters.tube α β R)
  let j := SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R)
  let H := TopCat.Homotopy.comp (TopCat.Homotopy.refl (nearSource α β R)) (AnnularTimeTrim.cylinder X)
  let K := TopCat.Homotopy.comp (AnnularTimeTrim.cylinder (TopCat.of (P × Q))) (TopCat.Homotopy.refl j)
  have he : H.h = K.h := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_post (AnnularTimeTrim.cylinder X) (nearSource α β R) q).trans
    ((TimePrismNaturality.prism_congr H K he q).trans
      (TimePrismNaturality.prism_pre (AnnularTimeTrim.cylinder (TopCat.of (P × Q))) j q).symm)

end
end Finsler.OriginalFirstHalfAnnularJoinCover
