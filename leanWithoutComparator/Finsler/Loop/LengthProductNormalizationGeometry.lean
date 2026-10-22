module

public import Finsler.Loop.StrictLengthLoopProduct
public import Finsler.Topology.DiagonalCutNaturality

/-! The actual pair normalization fixes both sphere evaluations and
the literal diagonal cochain. Its genuine strong-H1 homotopy preserves
every basepoint-distance tube and each separate strict length bound. -/

@[expose] public section
namespace Finsler.LengthProductNormalizationGeometry

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge Finsler.StrictLengthLoopProduct
open Finsler.CompactH1Alignment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ)

def leftEvaluation : pairSpace F p q ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => H1FiberBase.point z.1.val,
    H1FiberBase.continuous_point.comp (continuous_subtype_val.comp continuous_fst)⟩

def rightEvaluation : pairSpace F p q ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => H1FiberBase.point z.2.val,
    H1FiberBase.continuous_point.comp (continuous_subtype_val.comp continuous_snd)⟩

theorem pairMap_left : pairMap F p q ≫ FilteredLoopProduct.leftEvaluation F p q = leftEvaluation F p q := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact normLoop_point F 1 z.1.val

theorem pairMap_right : pairMap F p q ≫ FilteredLoopProduct.rightEvaluation F p q = rightEvaluation F p q := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact normLoop_point F 1 z.2.val

theorem cocycle_energy (hn : 1 ≤ n) :
    cochainPullback (pairMap F p q) n (DiagonalPullbackCut.cocycle hn
      (FilteredLoopProduct.leftEvaluation F p q) (FilteredLoopProduct.rightEvaluation F p q)) =
    DiagonalPullbackCut.cocycle hn (leftEvaluation F p q) (rightEvaluation F p q) := by
  rw [← DiagonalCutNaturality.cocycle_pullback, pairMap_left, pairMap_right]

variable (hp : 0 < p) (hq : 0 < q)

def pairHomotopy : TopCat.Homotopy (𝟙 (pairSpace F p q))
    (pairMap F p q ≫ (toLength F p hp ⊗ₘ toLength F q hq)) :=
  (shortHomotopy F p hp).prodMap (shortHomotopy F q hq)

def atTime (t : ClosedInterval) : pairSpace F p q ⟶ pairSpace F p q :=
  TopCat.ofHom ⟨fun z => pairHomotopy F p q hp hq (t, z),
    (pairHomotopy F p q hp hq).continuous.comp (continuous_const.prodMk continuous_id)⟩

theorem atTime_zero : atTime F p q hp hq 0 = 𝟙 (pairSpace F p q) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact (pairHomotopy F p q hp hq).map_zero_left z

theorem atTime_one : atTime F p q hp hq 1 = pairMap F p q ≫ (toLength F p hp ⊗ₘ toLength F q hq) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact (pairHomotopy F p q hp hq).map_one_left z

theorem atTime_left (t : ClosedInterval) :
    atTime F p q hp hq t ≫ leftEvaluation F p q = leftEvaluation F p q := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact normLoop_point F t.val z.1.val

theorem atTime_right (t : ClosedInterval) :
    atTime F p q hp hq t ≫ rightEvaluation F p q = rightEvaluation F p q := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact normLoop_point F t.val z.2.val

theorem cocycle_time (hn : 1 ≤ n) (t : ClosedInterval) :
    cochainPullback (atTime F p q hp hq t) n
      (DiagonalPullbackCut.cocycle hn (leftEvaluation F p q) (rightEvaluation F p q)) =
    DiagonalPullbackCut.cocycle hn (leftEvaluation F p q) (rightEvaluation F p q) := by
  rw [← DiagonalCutNaturality.cocycle_pullback, atTime_left, atTime_right]

def near (R : ℝ) : Set (pairSpace F p q) := {z | dist (basepoint z.1.val) (basepoint z.2.val) < R}

theorem near_open (R : ℝ) : IsOpen (near F p q R) :=
  isOpen_lt ((H1AlignmentHomotopy.basepoint_continuous.comp (continuous_subtype_val.comp continuous_fst)).dist
    (H1AlignmentHomotopy.basepoint_continuous.comp (continuous_subtype_val.comp continuous_snd))) continuous_const

theorem atTime_near (R : ℝ) (t : ClosedInterval) :
    Set.MapsTo (atTime F p q hp hq t) (near F p q R) (near F p q R) := by
  intro z hz
  change dist (basepoint (NormalizationHomotopy.normLoop F (t.val, z.1.val)))
    (basepoint (NormalizationHomotopy.normLoop F (t.val, z.2.val))) < R
  rw [normLoop_basepoint, normLoop_basepoint]
  exact hz

def nearAtTime (R : ℝ) (t : ClosedInterval) :=
  restriction (atTime F p q hp hq t) (near F p q R) (near F p q R) (atTime_near F p q hp hq R t)

def nearHomotopy (R : ℝ) : TopCat.Homotopy (𝟙 (TopCat.of (near F p q R))) (nearAtTime F p q hp hq R 1) where
  toFun z := ⟨pairHomotopy F p q hp hq (z.1, z.2.val), atTime_near F p q hp hq R z.1 z.2.property⟩
  continuous_toFun := ((pairHomotopy F p q hp hq).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left z := Subtype.ext ((pairHomotopy F p q hp hq).map_zero_left z.val)
  map_one_left _ := rfl

theorem nearHomotopy_length_left (R : ℝ) (t : ClosedInterval) (z : near F p q R) :
    SobolevLength.length F ((nearHomotopy F p q hp hq R) (t, z)).val.1.val = SobolevLength.length F z.val.1.val :=
  NormalizationHomotopy.length_normLoop F (t.val, z.val.1.val)

theorem nearHomotopy_length_right (R : ℝ) (t : ClosedInterval) (z : near F p q R) :
    SobolevLength.length F ((nearHomotopy F p q hp hq R) (t, z)).val.2.val = SobolevLength.length F z.val.2.val :=
  NormalizationHomotopy.length_normLoop F (t.val, z.val.2.val)

end
end Finsler.LengthProductNormalizationGeometry
