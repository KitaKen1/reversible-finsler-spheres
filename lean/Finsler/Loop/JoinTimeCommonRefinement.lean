module

public import Finsler.Loop.FullSecondHalfAnnularInputs
public import Finsler.Loop.CompactNearJoinParameters
public import Finsler.Loop.SmallCapSubspaceLift

/-! An actual open full cover on the original product-time source.
Its near members map into the genuine native face cover; its remaining
member is join-far, where the genuine first cap is zero. Thus every
nonzero whole parent enters one target native small-chain carrier. -/

@[expose] public section
namespace Finsler.JoinTimeCommonRefinement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R η : ℝ)

def source : TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶
    TopCat.of (P × (ClosedInterval × Q)) :=
  CompactNearJoinParameters.timeMap α β R ≫
    SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q))) (OriginalSecondHalfCompactTube.tube α β R)

def oldCover (i : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    Set (OriginalSecondHalfCompactTube.tube α β R) :=
  CompactNearJoinParameters.timeInv α β R ⁻¹'
    SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η i

theorem oldCover_open (i : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    IsOpen (oldCover α β R η i) :=
  (FullSecondHalfAnnularInputs.faceCover_open (CompactNearJoinParameters.tube α β R) η i).preimage
    (CompactNearJoinParameters.timeInv α β R).hom.continuous

theorem exists_extension (i : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    ∃ W : Set (P × (ClosedInterval × Q)), IsOpen W ∧
      Subtype.val ⁻¹' W = oldCover α β R η i :=
  isOpen_induced_iff.mp (oldCover_open α β R η i)

def extension (i : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    Set (P × (ClosedInterval × Q)) := (exists_extension α β R η i).choose

theorem extension_open (i : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    IsOpen (extension α β R η i) := (exists_extension α β R η i).choose_spec.1

theorem extension_preimage (i : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) :
    Subtype.val ⁻¹' extension α β R η i = oldCover α β R η i :=
  (exists_extension α β R η i).choose_spec.2

def nearSet : Set (P × (ClosedInterval × Q)) :=
  {z | dist (basepoint (α z.1)) (basepoint (β z.2.2)) < R}

def farSet (κ : ℝ) : Set (P × (ClosedInterval × Q)) :=
  {z | κ < dist (basepoint (α z.1)) (basepoint (β z.2.2))}

def cover (κ : ℝ) : Option (JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) →
    Set (P × (ClosedInterval × Q)) := fun i =>
  match i with
  | none => farSet α β κ
  | some i => extension α β R η i ∩ nearSet α β R

theorem cover_open (κ : ℝ) (i : Option (JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R))) :
    IsOpen (cover α β R η κ i) := by
  have hd : Continuous (fun z : P × (ClosedInterval × Q) =>
      dist (basepoint (α z.1)) (basepoint (β z.2.2))) :=
    (H1AlignmentHomotopy.basepoint_continuous.comp (α.continuous.comp continuous_fst)).dist
      (H1AlignmentHomotopy.basepoint_continuous.comp (β.continuous.comp (continuous_snd.comp continuous_snd)))
  cases i with
  | none => exact isOpen_lt continuous_const hd
  | some i => exact (extension_open α β R η i).inter (isOpen_lt hd continuous_const)

theorem cover_univ (hη : 0 < η) {κ : ℝ} (hκR : κ < R) :
    ⋃ i, cover α β R η κ i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : dist (basepoint (α z.1)) (basepoint (β z.2.2)) < R
  · let zK : OriginalSecondHalfCompactTube.tube α β R := ⟨z, hz.le⟩
    let y := CompactNearJoinParameters.timeInv α β R zK
    have hy : y ∈ ⋃ i, SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η i := by
      rw [FullSecondHalfAnnularInputs.faceCover_univ _ η hη]
      exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨some i, ?_, hz⟩
    have hi' : zK ∈ oldCover α β R η i := hi
    rw [← extension_preimage α β R η i] at hi'
    exact hi'
  · exact Set.mem_iUnion.mpr ⟨none, hκR.trans_le (le_of_not_gt hz)⟩

theorem near_image (i : JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) {κ : ℝ} :
    cover α β R η κ (some i) ⊆ source α β R ''
      SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η i := by
  intro z hz
  have hzR : dist (basepoint (α z.1)) (basepoint (β z.2.2)) < R := hz.2
  let zK : OriginalSecondHalfCompactTube.tube α β R := ⟨z, hzR.le⟩
  have hi : CompactNearJoinParameters.timeInv α β R zK ∈
      SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η i := by
    change zK ∈ oldCover α β R η i
    rw [← extension_preimage α β R η i]
    exact hz.1
  refine ⟨CompactNearJoinParameters.timeInv α β R zK, hi, ?_⟩
  have he := ConcreteCategory.congr_hom (CompactNearJoinParameters.timeInv_timeMap α β R) zK
  exact congrArg Subtype.val he

theorem parent_control (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (q : ℕ)
    (σ : ((TopCat.of (P × (ClosedInterval × Q))).smallSingularSubcomplex (cover α β R η κ) : SSet) _⦋n + q⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (P × (ClosedInterval × Q)))).ιChainComplex σ.val ≫
      absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n q (n + q) rfl
        (CompactJoinCocycle.timeCocycle α β hn hκ) ≠ 0) :
    ∃ i, Set.range ((TopCat.of (P × (ClosedInterval × Q))).toSSetObjEquiv _ σ.val) ⊆
      source α β R '' SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η i := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff
    (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η κ) σ.val).mp σ.property
  cases i with
  | none =>
    have hfar : Set.range ((TopCat.of (P × (ClosedInterval × Q))).toSSetObjEquiv _ σ.val) ⊆
        NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) κ :=
      fun z hz => (show κ < dist (basepoint (α z.1)) (basepoint (β z.2.2)) from hi hz).le
    exact (hσ (SupportedCap.cap_zero_on_simplex _ _ n q (n + q) rfl
      (CompactJoinCocycle.timeCocycle α β hn hκ)
      (CompactJoinCocycle.timeCocycle_far_zero α β hn hκ) σ.val hfar)).elim
  | some i => exact ⟨i, hi.trans (near_image α β R η i)⟩

def cap (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) :
    DegreeLoweringHomology.Map
      (small (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η κ))
      (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)) n :=
  SmallCapSubspaceLift.operation
    (TopCat.of (P × (ClosedInterval × Q)))
    (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (OriginalSecondHalfCompactTube.tube α β R) (CompactNearJoinParameters.timeIso α β R)
    (cover α β R η κ) (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
    n (CompactJoinCocycle.timeCocycle α β hn hκ)
    (fun q σ hσ => parent_control α β R η hn hκ q σ hσ)
    (CompactJoinCocycle.timeCocycle_closed α β hn hκ)

theorem cap_source (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (q : ℕ) :
    (cap α β R η hn hκ).component q ≫
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) ≫
          push (source α β R)).f q =
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η κ)).f (n + q) ≫
        absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n q (n + q) rfl
          (CompactJoinCocycle.timeCocycle α β hn hκ) :=
  SmallCapSubspaceLift.component_inclusion
    (TopCat.of (P × (ClosedInterval × Q)))
    (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (OriginalSecondHalfCompactTube.tube α β R) (CompactNearJoinParameters.timeIso α β R)
    (cover α β R η κ) (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
    n (CompactJoinCocycle.timeCocycle α β hn hκ)
    (fun q σ hσ => parent_control α β R η hn hκ q σ hσ) q

end
end Finsler.JoinTimeCommonRefinement
