module

public import Finsler.Loop.ClosedPathPauseFormulas
public import Finsler.Loop.H1PathRepresentativeCalculus
public import Finsler.Topology.SupportedSelfCut

/-! On the ACTUAL self-coincidence locus, the ORIGINAL strong-H1
tested/retained loops are precisely the prefix/suffix closed paths
with back/front pauses. This supplies actual ordinary homotopies
removing those pauses; it does not compute the Thom cap contribution. -/
@[expose] public section
namespace Finsler.DiagonalSelfCutRepresentatives
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevAffine
open Finsler.ClosedLoopReparametrization Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

local notation "I" => ClosedInterval
abbrev domain (n : ℕ) : TopCat.{0} :=
  TopCat.of {z : SelfCutThomCocycle.parameters n // endpoint z = point z.2}

def intoTube {n : ℕ} (z : domain n) : tube n :=
  ⟨z.val, by change ‖(endpoint z.val : Ambient n) - (point z.val.2 : Ambient n)‖ < 1
             rw [z.property, sub_self, norm_zero]; norm_num⟩

theorem continuous_intoTube (n : ℕ) : Continuous (intoTube (n := n)) :=
  continuous_subtype_val.subtype_mk _

def prefixTime (c s : I) : I :=
  ⟨(c : ℝ) * s, ⟨mul_nonneg c.property.1 s.property.1,
    (mul_le_of_le_one_right c.property.1 s.property.2).trans c.property.2⟩⟩

def suffixTime (c s : I) : I :=
  ⟨aff c 1 s, aff_mem_Icc c.property (by norm_num) s.property⟩

theorem prefixTime_zero (c : I) : prefixTime c 0 = 0 := by
  apply Subtype.ext
  simp [prefixTime]
theorem prefixTime_one (c : I) : prefixTime c 1 = c := by
  apply Subtype.ext
  simp [prefixTime]
theorem suffixTime_zero (c : I) : suffixTime c 0 = c := by
  apply Subtype.ext
  exact aff_zero _ _
theorem suffixTime_one (c : I) : suffixTime c 1 = 1 := by
  apply Subtype.ext
  exact aff_one _ _

theorem continuous_prefixEvaluation (n : ℕ) : Continuous
    (fun z : domain n × I => sphereRepresentative z.1.val.2 (prefixTime z.1.val.1 z.2)) := by
  have ht : Continuous (fun z : domain n × I => prefixTime z.1.val.1 z.2) := by
    unfold prefixTime
    fun_prop
  have hu : Continuous (fun z : domain n × I => z.1.val.2) := by fun_prop
  exact continuous_endpoint.comp (ht.prodMk hu)

theorem continuous_suffixEvaluation (n : ℕ) : Continuous
    (fun z : domain n × I => sphereRepresentative z.1.val.2 (suffixTime z.1.val.1 z.2)) := by
  have ht : Continuous (fun z : domain n × I => suffixTime z.1.val.1 z.2) := by
    unfold suffixTime aff
    fun_prop
  have hu : Continuous (fun z : domain n × I => z.1.val.2) := by fun_prop
  exact continuous_endpoint.comp (ht.prodMk hu)

def prefixClosed {n : ℕ} (z : domain n) : ClosedPathCircle.closedMaps (Sphere n) :=
  ⟨⟨fun s => sphereRepresentative z.val.2 (prefixTime z.val.1 s),
    (continuous_prefixEvaluation n).comp (continuous_const.prodMk continuous_id)⟩, by
    change sphereRepresentative z.val.2 (prefixTime z.val.1 0) =
      sphereRepresentative z.val.2 (prefixTime z.val.1 1)
    rw [prefixTime_zero, prefixTime_one]
    exact z.property.symm⟩

def suffixClosed {n : ℕ} (z : domain n) : ClosedPathCircle.closedMaps (Sphere n) :=
  ⟨⟨fun s => sphereRepresentative z.val.2 (suffixTime z.val.1 s),
    (continuous_suffixEvaluation n).comp (continuous_const.prodMk continuous_id)⟩, by
    change sphereRepresentative z.val.2 (suffixTime z.val.1 0) =
      sphereRepresentative z.val.2 (suffixTime z.val.1 1)
    rw [suffixTime_zero, suffixTime_one]
    exact z.property.trans (sphereRepresentative_endpoints z.val.2).symm⟩

theorem continuous_prefixClosed (n : ℕ) : Continuous (prefixClosed (n := n)) := by
  apply Continuous.subtype_mk
  exact ContinuousMap.continuous_of_continuous_uncurry _ (continuous_prefixEvaluation n)

theorem continuous_suffixClosed (n : ℕ) : Continuous (suffixClosed (n := n)) := by
  apply Continuous.subtype_mk
  exact ContinuousMap.continuous_of_continuous_uncurry _ (continuous_suffixEvaluation n)

def prefixPath {n : ℕ} (z : domain n) : Path (point z.val.2) (point z.val.2) where
  toFun := (prefixClosed z).val
  continuous_toFun := (prefixClosed z).val.continuous
  source' := by change sphereRepresentative z.val.2 (prefixTime z.val.1 0) = _; rw [prefixTime_zero]; rfl
  target' := by change sphereRepresentative z.val.2 (prefixTime z.val.1 1) = _; rw [prefixTime_one]; exact z.property

def suffixPath {n : ℕ} (z : domain n) : Path (point z.val.2) (point z.val.2) where
  toFun := (suffixClosed z).val
  continuous_toFun := (suffixClosed z).val.continuous
  source' := by change sphereRepresentative z.val.2 (suffixTime z.val.1 0) = _; rw [suffixTime_zero]; exact z.property
  target' := by change sphereRepresentative z.val.2 (suffixTime z.val.1 1) = _; rw [suffixTime_one]; exact sphereRepresentative_endpoints z.val.2

theorem representative_prefix {n : ℕ} (z : domain n) (s : I) :
    continuousRepresentative (H1SelfCutNeighborhood.prefixPath (intoTube z)) (s : ℝ) =
      (prefixPath z s : Ambient n) := by
  rw [H1SelfCutNeighborhood.prefixPath,
    representative_restrict _ (by norm_num) z.val.1.property z.val.1.property.1 s.property]
  change continuousRepresentative (z.val.2.data : Space n) (aff 0 z.val.1 s) =
    continuousRepresentative (z.val.2.data : Space n) ((z.val.1 : ℝ) * s)
  simp [aff]

theorem representative_suffix {n : ℕ} (z : domain n) (s : I) :
    continuousRepresentative (H1SelfCutNeighborhood.suffixPath (intoTube z)) (s : ℝ) =
      (suffixPath z s : Ambient n) := by
  rw [H1SelfCutNeighborhood.suffixPath,
    representative_restrict _ z.val.1.property (by norm_num) z.val.1.property.2 s.property]
  rfl

theorem representative_left {n : ℕ} (z : domain n) (s : I) :
    continuousRepresentative (leftData (intoTube z)) (s : ℝ) =
      ((prefixPath z).trans (Path.refl (point z.val.2)) s : Ambient n) := by
  apply H1PathRepresentativeCalculus.represented_concat _ _ _ _
    (representative_prefix z) _ s
  intro t
  change continuousRepresentative (H1ShortArc.arc (endpoint z.val) (point z.val.2)) (t : ℝ) = _
  rw [z.property, H1ShortArc.arc_self, continuousRepresentative_constantData _ t.property]
  rfl

theorem representative_right {n : ℕ} (z : domain n) (s : I) :
    continuousRepresentative (rightData (intoTube z)) (s : ℝ) =
      ((Path.refl (point z.val.2)).trans (suffixPath z) s : Ambient n) := by
  apply H1PathRepresentativeCalculus.represented_concat _ _ _ _ _ (representative_suffix z) s
  intro t
  change continuousRepresentative (H1ShortArc.arc (point z.val.2) (endpoint z.val)) (t : ℝ) = _
  rw [z.property, H1ShortArc.arc_self, continuousRepresentative_constantData _ t.property]
  rfl

def tested (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap (left (intoTube z)), by
    have hc := (sphereCircleMap_continuous n).comp (continuous_left.comp (continuous_intoTube n))
    exact hc⟩

def retained (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap (right (intoTube z)), by
    have hc := (sphereCircleMap_continuous n).comp (continuous_right.comp (continuous_intoTube n))
    exact hc⟩

def prefixFamily (n : ℕ) : domain n ⟶ TopCat.of (ClosedPathCircle.closedMaps (Sphere n)) :=
  TopCat.ofHom ⟨prefixClosed, continuous_prefixClosed n⟩
def suffixFamily (n : ℕ) : domain n ⟶ TopCat.of (ClosedPathCircle.closedMaps (Sphere n)) :=
  TopCat.ofHom ⟨suffixClosed, continuous_suffixClosed n⟩

theorem tested_factor (n : ℕ) : tested n = prefixFamily n ≫ circleMap n early := by
  ext z : 1
  have hp : (tested n) z = ClosedPathCircle.circle
      (ClosedPathCircle.ofPath ((prefixPath z).trans (Path.refl (point z.val.2)))) := by
    apply ContinuousMap.ext
    intro a
    change sphereCircleMap (left (intoTube z)) a = _
    rw [sphereCircleMap_point]
    rw [ClosedPathCircle.circle_apply]
    apply Subtype.ext
    exact representative_left z _
  exact hp.trans (ClosedPathPauseFormulas.circle_trans_refl (prefixPath z))

theorem retained_factor (n : ℕ) : retained n = suffixFamily n ≫ circleMap n late := by
  ext z : 1
  have hp : (retained n) z = ClosedPathCircle.circle
      (ClosedPathCircle.ofPath ((Path.refl (point z.val.2)).trans (suffixPath z))) := by
    apply ContinuousMap.ext
    intro a
    change sphereCircleMap (right (intoTube z)) a = _
    rw [sphereCircleMap_point]
    rw [ClosedPathCircle.circle_apply]
    apply Subtype.ext
    exact representative_right z _
  exact hp.trans (ClosedPathPauseFormulas.circle_refl_trans (suffixPath z))

def testedHomotopy (n : ℕ) : TopCat.Homotopy (tested n) (prefixFamily n ≫ circleMap n identity) := by
  rw [tested_factor]
  exact (homotopy n early identity).comp (TopCat.Homotopy.refl (prefixFamily n))

def retainedHomotopy (n : ℕ) : TopCat.Homotopy (retained n) (suffixFamily n ≫ circleMap n identity) := by
  rw [retained_factor]
  exact (homotopy n late identity).comp (TopCat.Homotopy.refl (suffixFamily n))

end
end Finsler.DiagonalSelfCutRepresentatives
