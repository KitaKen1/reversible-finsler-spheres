module

public import Finsler.Loop.FirstInputSelfCutTime
public import Finsler.Loop.OriginalFirstHalfCutOutputJoinData

/-! The actual individually bounded first-cut space in the original
cylinder, its proper carrier, source, and retained short-loop map. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedSpace

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (F : ReversibleMetric (m + 1)) (B : ℝ)

def bounded : Set (ambient α) := {z | ∃ hz : z ∈ CompactRotatedCutData.source α r,
  SobolevLength.length F (OriginalFirstHalfCutOutputJoinData.kept α r hr ⟨z, hz⟩) < B}

def toCut : TopCat.of (bounded α r hr F B) ⟶ OriginalFirstHalfCutNormalizedFactors.cutSpace α r :=
  TopCat.ofHom ⟨fun z => ⟨z.val, z.property.choose⟩, by fun_prop⟩

def source : TopCat.of (bounded α r hr F B) ⟶ ambient α :=
  SupportedCap.subspaceMap (ambient α) (bounded α r hr F B)

theorem source_square : toCut α r hr F B ≫ FirstInputSelfCutCochains.source α r = source α r hr F B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def retained : TopCat.of (bounded α r hr F B) ⟶ TopCat.of (SelfCutOscillation.short F B) :=
  TopCat.ofHom ⟨fun z => ⟨OriginalFirstHalfCutOutputJoinData.kept α r hr (toCut α r hr F B z),
    z.property.choose_spec⟩,
    ((OriginalFirstHalfCutOutputJoinData.kept α r hr).continuous.comp
      (toCut α r hr F B).hom.continuous).subtype_mk _⟩

def carrier (κ : ℝ) (i : CompactRotatedCutData.source α r) : Set (TopCat.of (bounded α r hr F B)) :=
  toCut α r hr F B ⁻¹' FirstInputSelfCutCover.carrier α r hr κ i

theorem carrier_open (κ : ℝ) (i : CompactRotatedCutData.source α r) : IsOpen (carrier α r hr F B κ i) :=
  (FirstInputSelfCutCover.carrier_open α r hr κ i).preimage (toCut α r hr F B).hom.continuous

theorem carrier_univ {κ : ℝ} (hκ : 0 < κ) : ⋃ i, carrier α r hr F B κ i = Set.univ := by
  simp only [carrier, ← Set.preimage_iUnion, FirstInputSelfCutCover.carrier_univ α r hr κ hκ, Set.preimage_univ]

def toProperSmall (κ : ℝ) := SmallRetractionComparison.map
  (carrier α r hr F B κ) (FirstInputSelfCutCover.carrier α r hr κ) (toCut α r hr F B)
  (fun i => i) (fun _ _ hz => hz)

def sourceChain (κ : ℝ) :=
  inclusion (TopCat.of (bounded α r hr F B)) (carrier α r hr F B κ) ≫ push (source α r hr F B)

theorem sourceChain_mono (κ : ℝ) (q : ℕ) : Mono ((sourceChain α r hr F B κ).f q) := by
  have hh := SmallCapSubspaceLift.target_mono (ambient α) (TopCat.of (bounded α r hr F B))
    (bounded α r hr F B) (Iso.refl _) (carrier α r hr F B κ) q
  simpa only [sourceChain, source, SmallCapSubspaceLift.target, SmallCapSubspaceLift.source,
    Iso.refl_hom, Category.id_comp] using hh

theorem proper_source_square (κ : ℝ) :
    toProperSmall α r hr F B κ ≫ FirstInputSelfCutTime.sourceMap α r hr κ = sourceChain α r hr F B κ := by
  have hh := SmallRetractionComparison.map_inclusion (carrier α r hr F B κ)
    (FirstInputSelfCutCover.carrier α r hr κ) (toCut α r hr F B) (fun i => i) (fun _ _ hz => hz)
  change toProperSmall α r hr F B κ ≫
    inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (FirstInputSelfCutCover.carrier α r hr κ) = _ at hh
  rw [FirstInputSelfCutTime.sourceMap, ← Category.assoc, hh, Category.assoc,
    ← push_comp, source_square]
  rfl

end
end Finsler.FirstInputSelfCutBoundedSpace
