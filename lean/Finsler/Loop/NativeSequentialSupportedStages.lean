module

public import Finsler.Loop.NativeSequentialCollarGeometry
public import Finsler.Loop.NativeOrderedDoubleCutSupported

/-! TWO ACTUAL original normalized supported Thom-cap stages on the
full raw-half sequential source. First cut the original loop; second
cut its ORIGINAL tested prefix or retained suffix at the actual half
clock. The final near maps land in the exact Stage96 original domains.
No operation is replaced by the common ordered cap order here. -/
@[expose] public section
namespace Finsler.NativeSequentialSupportedStages
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.NativeSequentialCutParameters
open Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 750000

abbrev source (n : ℕ) := TopCat.of (SelfCutThomCocycle.parameters n × ClosedInterval)

def firstParameter (n : ℕ) : source n ⟶ SelfCutThomCocycle.parameters n :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev radius := NativeClosingArcPowerVanishing.radius m hm F
abbrev outerSpace := TopCat.of (NativeOrderedDoubleCutSupported.near (firstParameter (m + 1)) (radius m hm F))

def outer : outerSpace m hm F ⟶ NativeSequentialCutParameters.source (m + 1) := TopCat.ofHom
  ⟨fun z => (⟨z.val.1, z.property.trans_le (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)⟩, z.val.2),
    by fun_prop⟩

def firstOperation := NativeOrderedDoubleCutSupported.operation (firstParameter (m + 1)) (by omega)
  (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)

def prefixParameter : outerSpace m hm F ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  outer m hm F ≫ NativeSequentialCutParameters.prefixParameter (m + 1)

def suffixParameter : outerSpace m hm F ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  outer m hm F ≫ NativeSequentialCutParameters.suffixParameter (m + 1)

def prefixOperation := NativeOrderedDoubleCutSupported.operation (prefixParameter m hm F) (by omega)
  (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)

def suffixOperation := NativeOrderedDoubleCutSupported.operation (suffixParameter m hm F) (by omega)
  (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)

theorem prefix_final_mem
    (z : NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) (radius m hm F)) :
    outer m hm F z.val ∈ NativeSequentialCutParameters.prefixNear (m + 1) (radius m hm F) := by
  constructor
  · exact z.val.property
  · have h : SupportedSelfCut.distance (m + 1)
        (NativeSequentialCutParameters.prefixParameter (m + 1) (outer m hm F z.val)) < radius m hm F := z.property
    rw [NativeSequentialCutParameters.prefix_distance] at h
    exact h

theorem suffix_final_mem
    (z : NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) (radius m hm F)) :
    outer m hm F z.val ∈ NativeSequentialCutParameters.suffixNear (m + 1) (radius m hm F) := by
  constructor
  · exact z.val.property
  · have h : SupportedSelfCut.distance (m + 1)
        (NativeSequentialCutParameters.suffixParameter (m + 1) (outer m hm F z.val)) < radius m hm F := z.property
    rw [NativeSequentialCutParameters.suffix_distance] at h
    exact h

def prefixFinal : TopCat.of (NativeOrderedDoubleCutSupported.near (prefixParameter m hm F) (radius m hm F)) ⟶
    NativeSequentialCollarGeometry.prefixSource m hm F := TopCat.ofHom
  ⟨fun z => ⟨outer m hm F z.val, prefix_final_mem m hm F z⟩,
    ((outer m hm F).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def suffixFinal : TopCat.of (NativeOrderedDoubleCutSupported.near (suffixParameter m hm F) (radius m hm F)) ⟶
    NativeSequentialCollarGeometry.suffixSource m hm F := TopCat.ofHom
  ⟨fun z => ⟨outer m hm F z.val, suffix_final_mem m hm F z⟩,
    ((outer m hm F).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem prefix_thom_original_clock :
    cochainPullback (prefixParameter m hm F) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) =
    cochainPullback (outer m hm F ≫ NativeSequentialCutParameters.prefixOriginal (m + 1)) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) := by
  rw [prefixParameter, pullback_comp, NativeSequentialCutParameters.prefix_thom, ← pullback_comp]

theorem suffix_thom_original_clock :
    cochainPullback (suffixParameter m hm F) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) =
    cochainPullback (outer m hm F ≫ NativeSequentialCutParameters.suffixOriginal (m + 1)) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) := by
  rw [suffixParameter, pullback_comp, NativeSequentialCutParameters.suffix_thom, ← pullback_comp]

end
end Finsler.NativeSequentialSupportedStages
