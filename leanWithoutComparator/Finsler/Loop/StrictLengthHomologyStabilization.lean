module

public import Finsler.Loop.CompactHomologyZeroDetection
public import Finsler.Loop.LengthFilteredLoopRotation
public import Finsler.Analysis.CompactH1Alignment

/-! The ACTUAL strict Finsler length filtration computes the homology
of the ACTUAL strong-H1 loop space. Equality of two actual filtered
classes in the full space is witnessed at one finite common length.
This is equality detection, not injectivity of any fixed sublevel. -/
@[expose] public section
namespace Finsler.StrictLengthHomologyStabilization
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology TopologicalSpace SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable {n : ℕ} (F : ReversibleMetric n)

def diagram : ℝ ⥤ TopCat.{0} where
  obj a := lengthSpace F a
  map f := LengthFilteredLoopRotation.cut F f.le
  map_id _ := by ext x : 1; rfl
  map_comp _ _ := by ext x : 1; rfl

def cocone : Cocone (diagram F) where
  pt := Loops n
  ι := { app a := LengthFilteredLoopRotation.full F a
         naturality := by intro a b f; ext x : 1; rfl }

theorem leg_embedding (a : ℝ) : IsEmbedding ((cocone F).ι.app a) :=
  IsEmbedding.subtypeVal

theorem absorbs_compact (K : Set (Loops n)) (hK : IsCompact K) :
    ∃ a : ℝ, K ⊆ Set.range ((cocone F).ι.app a) := by
  obtain ⟨M, _, hM⟩ := CompactH1Alignment.exists_length_bound F hK
    (fun u : Loops n => u) continuous_id.continuousOn
  refine ⟨M + 1, ?_⟩
  intro u hu
  exact ⟨⟨u, (hM u hu).trans_lt (by linarith)⟩, rfl⟩

def homologyColimit (q : ℕ) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).mapCocone
      (cocone F)) :=
  DirectedCompactHomology.homology coeff q (cocone F) (leg_embedding F) (absorbs_compact F)

theorem exists_equal (q : ℕ) {a b : ℝ}
    (x : homologyZMod2 (lengthSpace F a) q) (y : homologyZMod2 (lengthSpace F b) q)
    (he : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) q).hom x =
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) q).hom y) :
    ∃ B : ℝ, ∃ ha : a ≤ B, ∃ hb : b ≤ B,
      (homologyPushZMod2 (LengthFilteredLoopRotation.cut F ha) q).hom x =
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hb) q).hom y := by
  have : PreservesFilteredColimitsOfSize.{0,0} (forget (ModuleCat.{0} (ZMod 2))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let C := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).mapCocone (cocone F)
  have he' : C.ι.app a x = C.ι.app b y := he
  obtain ⟨B, f, g, hB⟩ := ((homologyColimit F q).eq_iff _).mp he'
  exact ⟨B, f.le, g.le, hB⟩

end
end Finsler.StrictLengthHomologyStabilization
