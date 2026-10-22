module

public import Finsler.Loop.CompactInputShortMaps
public import Finsler.Loop.SingleCutCanonicalThomCochains
public import Finsler.Topology.SmallRetractionComparison

/-! The real proper compact-family cut maps to the canonical incoming
tube. Both cut loops are radius-independent literal maps on this common
proper domain. Pull back the actual tested oscillation cover there. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalIncoming

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputSelfCutCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (a R : ℝ) (hrR : r < R)
  (hA : ∀ x, SobolevLength.length F (α x) < a)

def toNear : OriginalFirstHalfCutNormalizedFactors.cutSpace α r ⟶
    TopCat.of (FilteredPrismSelfCut.near F a R) :=
  TopCat.ofHom ⟨fun z => ⟨CompactInputShortMaps.cylinder α F a hA z.val, z.property.trans_lt hrR⟩,
    ((CompactInputShortMaps.cylinder α F a hA).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem near_square : toNear α r F a R hrR hA ≫
    SupportedCap.subspaceMap (FilteredPrismSelfCut.domain F a) (FilteredPrismSelfCut.near F a R) =
      source α r ≫ CompactInputShortMaps.cylinder α F a hA := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def incoming := toNear α r F a R hrR hA ≫ FilteredPrismSelfCut.toIncoming F R a

theorem incoming_evaluation : incoming α r F a R hrR hA ≫ FilteredTestedCap.inclusion F R a ≫
    SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) (SupportedSelfCut.neighborhood (m + 1) R) =
      FirstInputRotationOriginalFactors.originalEvaluation α r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (hR : R ≤ 1)

theorem tested_square : incoming α r F a R hrR hA ≫ FilteredTestedCap.inclusion F R a ≫
    TopCat.ofHom (SupportedSelfCut.tested (m + 1) hR) =
      FirstInputRotationOriginalFactors.originalTester α r hr := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem retained_square : incoming α r F a R hrR hA ≫ FilteredTestedCap.retainedMap F hR a =
    TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem cochain_source (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) :
    cochainPullback (incoming α r F a R hrR hA) p (FilteredTestedCap.cochain F hR a p T) =
      cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T := by
  rw [FilteredTestedCap.cochain, NormalizedSelfCut.testedCocycle, ← pullback_comp, ← pullback_comp,
    Category.assoc, tested_square]

def cover (ε : ℝ) (i : SupportedSelfCut.neighborhood (m + 1) R) :
    Set (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) :=
  incoming α r F a R hrR hA ⁻¹' FilteredTestedCap.cover F hR a ε i

theorem cover_open (ε : ℝ) (i : SupportedSelfCut.neighborhood (m + 1) R) :
    IsOpen (cover α r F a R hrR hA hR ε i) :=
  (FilteredTestedCap.cover_open F hR a ε i).preimage (incoming α r F a R hrR hA).hom.continuous

theorem cover_univ {ε : ℝ} (hε : 0 < ε) :
    ⋃ i, cover α r F a R hrR hA hR ε i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hz : incoming α r F a R hrR hA z ∈ ⋃ i, FilteredTestedCap.cover F hR a ε i :=
    (FilteredTestedCap.cover_univ F hR a hε).symm ▸ Set.mem_univ _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

def smallMap (ε : ℝ) := SmallRetractionComparison.map
  (cover α r F a R hrR hA hR ε) (FilteredTestedCap.cover F hR a ε)
  (incoming α r F a R hrR hA) id (fun _ _ hz => hz)

theorem smallMap_source (ε : ℝ) :
    smallMap α r F a R hrR hA hR ε ≫ inclusion (FilteredTestedCap.space F R a) (FilteredTestedCap.cover F hR a ε) =
    inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (cover α r F a R hrR hA hR ε) ≫
      push (incoming α r F a R hrR hA) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

end
end Finsler.SingleCutCanonicalIncoming
