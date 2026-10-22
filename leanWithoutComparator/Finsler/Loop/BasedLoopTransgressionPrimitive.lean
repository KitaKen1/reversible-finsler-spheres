module

public import Finsler.Loop.BasedMeridianProducts
public import Finsler.Loop.UncappedTimeSplit

/-! The ORIGINAL sphere-evaluation transgression is primitive under
actual based-path concatenation. The original full time prism splits
into the two actual path prisms plus an explicit triangle boundary.
No loop-space rank, Kunneth dimension, or GH algebra premise is used. -/
@[expose] public section
namespace Finsler.BasedLoopTransgressionPrimitive
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.BasedMeridianProducts
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

abbrev domain {n : ℕ} (P : Sphere n) : TopCat.{0} := space P ⊗ space P

def left {n : ℕ} (P : Sphere n) : domain P ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ ≫ forget P

def right {n : ℕ} (P : Sphere n) : domain P ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ ≫ forget P

def joined {n : ℕ} (P : Sphere n) : domain P ⟶ ContinuousLoopModel.space n :=
  concatenate P ≫ forget P

def timeMap {n : ℕ} {X : TopCat.{0}} (f : X ⟶ ContinuousLoopModel.space n) :=
  ((ContinuousLoopSweep.evaluationHomotopy n).comp (TopCat.Homotopy.refl f)).h

theorem timeMap_apply {n : ℕ} (P : Sphere n) (z : domain P ⊗ TopCat.I) :
    timeMap (joined P) z = (z.1.1.trans z.1.2) z.2.down :=
  ClosedPathCircle.circle_coe (ClosedPathCircle.ofPath (z.1.1.trans z.1.2)) z.2.down

theorem first_timeMap {n : ℕ} (P : Sphere n) :
    UncappedTimeSplit.first (timeMap (joined P)) = timeMap (left P) := by
  ext z : 1
  change timeMap (joined P) (z.1, IntervalTriangle.firstMap z.2) = _
  rw [timeMap_apply]
  change (z.1.1.trans z.1.2) ((IntervalTriangle.firstMap z.2).down) =
    ClosedPathCircle.circle (ClosedPathCircle.ofPath z.1.1) (((z.2.down : ℝ)) : SobolevCircleRepresentative.Circle)
  rw [ClosedPathCircle.circle_coe]
  rw [← Path.extend_apply _ (IntervalTriangle.firstMap z.2).down.property]
  change (z.1.1.trans z.1.2).extend ((z.2.down : ℝ) / 2) = _
  rw [Path.extend_trans_of_le_half _ _ (by linarith [z.2.down.property.2])]
  rw [show 2 * ((z.2.down : ℝ) / 2) = (z.2.down : ℝ) by ring]
  exact Path.extend_apply _ z.2.down.property

theorem second_timeMap {n : ℕ} (P : Sphere n) :
    UncappedTimeSplit.second (timeMap (joined P)) = timeMap (right P) := by
  ext z : 1
  change timeMap (joined P) (z.1, IntervalTriangle.secondMap z.2) = _
  rw [timeMap_apply]
  change (z.1.1.trans z.1.2) ((IntervalTriangle.secondMap z.2).down) =
    ClosedPathCircle.circle (ClosedPathCircle.ofPath z.1.2) (((z.2.down : ℝ)) : SobolevCircleRepresentative.Circle)
  rw [ClosedPathCircle.circle_coe]
  rw [← Path.extend_apply _ (IntervalTriangle.secondMap z.2).down.property]
  change (z.1.1.trans z.1.2).extend ((1 + (z.2.down : ℝ)) / 2) = _
  rw [Path.extend_trans_of_half_le _ _ (by linarith [z.2.down.property.1])]
  rw [show 2 * ((1 + (z.2.down : ℝ)) / 2) - 1 = (z.2.down : ℝ) by ring]
  exact Path.extend_apply _ z.2.down.property

theorem original_prism {n : ℕ} {X : TopCat.{0}} (f : X ⟶ ContinuousLoopModel.space n) (q : ℕ) :
    (push f).f q ≫ SelfHomotopySweep.component (ContinuousLoopSweep.chainHomotopy n) q =
      UncappedTimeSplit.component (timeMap f) q := by
  rw [timeMap, UncappedTimeSplit.prism_component]
  exact TimePrismNaturality.prism_pre (ContinuousLoopSweep.evaluationHomotopy n) f q

theorem original_split {n : ℕ} (P : Sphere n) (q : ℕ) :
    (chains (domain P)).iCycles q ≫
      ((push (joined P)).f q ≫ SelfHomotopySweep.component (ContinuousLoopSweep.chainHomotopy n) q) =
    (chains (domain P)).iCycles q ≫
      ((push (left P)).f q ≫ SelfHomotopySweep.component (ContinuousLoopSweep.chainHomotopy n) q) +
    (chains (domain P)).iCycles q ≫
      ((push (right P)).f q ≫ SelfHomotopySweep.component (ContinuousLoopSweep.chainHomotopy n) q) +
    ((chains (domain P)).iCycles q ≫ UncappedTimeSplit.comparison (timeMap (joined P)) q) ≫
      (chains (BorelEvaluation.sphere n)).d (q + 2) (q + 1) := by
  rw [original_prism, original_prism, original_prism,
    UncappedTimeSplit.full_split, first_timeMap, second_timeMap]

def cycleMap {n : ℕ} {X : TopCat.{0}} (f : X ⟶ ContinuousLoopModel.space n) (q : ℕ) :=
  HomologicalComplex.cyclesMap (push f) q ≫
    SelfHomotopySweep.cycles (ContinuousLoopSweep.chainHomotopy n) q

theorem cycleMap_i {n : ℕ} {X : TopCat.{0}} (f : X ⟶ ContinuousLoopModel.space n) (q : ℕ) :
    cycleMap f q ≫ (chains (BorelEvaluation.sphere n)).iCycles (q + 1) =
      (chains X).iCycles q ≫
        ((push f).f q ≫ SelfHomotopySweep.component (ContinuousLoopSweep.chainHomotopy n) q) := by
  rw [cycleMap, Category.assoc, SelfHomotopySweep.cycles_i, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc]

theorem cycles_split {n : ℕ} (P : Sphere n) (q : ℕ) :
    cycleMap (joined P) q = cycleMap (left P) q + cycleMap (right P) q +
      ((chains (domain P)).iCycles q ≫ UncappedTimeSplit.comparison (timeMap (joined P)) q) ≫
        (chains (BorelEvaluation.sphere n)).toCycles (q + 2) (q + 1) := by
  apply (cancel_mono ((chains (BorelEvaluation.sphere n)).iCycles (q + 1))).mp
  simp only [Preadditive.add_comp, cycleMap_i, Category.assoc, HomologicalComplex.toCycles_i]
  exact original_split P q

theorem homologyπ_sweep {n : ℕ} {X : TopCat.{0}} (f : X ⟶ ContinuousLoopModel.space n) (q : ℕ) :
    (chains X).homologyπ q ≫
      (homologyPushZMod2 f q ≫ ContinuousLoopSweep.homology n q) =
        cycleMap f q ≫ (chains (BorelEvaluation.sphere n)).homologyπ (q + 1) := by
  change (chains X).homologyπ q ≫
    (HomologicalComplex.homologyMap (push f) q ≫
      SelfHomotopySweep.homology (ContinuousLoopSweep.chainHomotopy n) q) = _
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    SelfHomotopySweep.homologyπ_homology, ← Category.assoc]
  rfl

theorem homology_split {n : ℕ} (P : Sphere n) (q : ℕ) :
    homologyPushZMod2 (joined P) q ≫ ContinuousLoopSweep.homology n q =
      homologyPushZMod2 (left P) q ≫ ContinuousLoopSweep.homology n q +
      homologyPushZMod2 (right P) q ≫ ContinuousLoopSweep.homology n q := by
  apply (cancel_epi ((chains (domain P)).homologyπ q)).mp
  rw [Preadditive.comp_add, homologyπ_sweep, homologyπ_sweep, homologyπ_sweep, cycles_split]
  simp only [Preadditive.add_comp, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero, add_zero]

theorem transgression_primitive {n : ℕ} (P : Sphere n) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (joined P) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (left P) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (right P) q).hom (ContinuousLoopSweep.transgression n q a) := by
  apply kroneckerMap_injective (domain P) q
  apply LinearMap.ext
  intro z
  have hpair (f : domain P ⟶ ContinuousLoopModel.space n) :
      (kroneckerMap (domain P) q).hom
        ((cohPullback f q).hom (ContinuousLoopSweep.transgression n q a)) z =
      (kroneckerMap (BorelEvaluation.sphere n) (q + 1)).hom a
        ((ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 f q).hom z)) := by
    have hn := congrArg (fun v : homologyDualZMod2 (domain P) q => v z)
      (kroneckerMap_naturality_apply f q (ContinuousLoopSweep.transgression n q a))
    exact hn.trans (ContinuousLoopSweep.pairing n q a ((homologyPushZMod2 f q).hom z))
  simp only [map_add, LinearMap.add_apply]
  rw [hpair, hpair, hpair]
  have h := ConcreteCategory.congr_hom (homology_split P q) z
  change (ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 (joined P) q).hom z) =
    (ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 (left P) q).hom z) +
    (ContinuousLoopSweep.homology n q).hom ((homologyPushZMod2 (right P) q).hom z) at h
  rw [h, map_add]

end
end Finsler.BasedLoopTransgressionPrimitive
