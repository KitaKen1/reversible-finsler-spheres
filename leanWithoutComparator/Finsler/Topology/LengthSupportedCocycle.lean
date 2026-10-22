module

public import Finsler.Topology.LengthEnergyMaps
public import Finsler.Topology.NormalizedRelativeRepresentative

/-! Construct the actual closed normalized T required by self-cutting from
an actual cohomology class whose restriction to the energy sublevel vanishes.
Arclength pullback changes energy support to length support and preserves
the absolute class. The resonance input giving the vanishing is not assumed
to have been proved here. -/

@[expose] public section
namespace Finsler.LengthSupportedCocycle

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SobolevReflectionAction Finsler.SelfCutOscillation
open scoped DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {n : ℕ} (F : ReversibleMetric n) {L : ℝ} (p : ℕ)
  (a : cohomologyZMod2 (TopCat.of (SphereLoop n)) p)
  (ha : (cohPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (energyCut F L)) p).hom a = 0)

def raw : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p :=
  cochainPullback (LengthEnergyMaps.normalizer F) p
    (NormalizedRelativeRepresentative.raw (TopCat.of (SphereLoop n)) (energyCut F L) p a ha)

theorem raw_closed :
    cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p (raw F p a ha) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (TopCat.of (SphereLoop n)))
    (singularCochainComplexZMod2.map (LengthEnergyMaps.normalizer F).op) p _
    (NormalizedRelativeRepresentative.raw_closed (TopCat.of (SphereLoop n)) (energyCut F L) p a ha)

theorem raw_supported (hL : 0 < L) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L)) p
      (raw F p a ha) = 0 := by
  rw [raw, ← SupportedCapNaturality.pullback_comp, LengthEnergyMaps.lengthToEnergy_factor F hL,
    SupportedCapNaturality.pullback_comp, NormalizedRelativeRepresentative.raw_supported]
  simp [cochainPullback]

theorem raw_class : CochainClass.classOf (cochainCxZMod2 (TopCat.of (SphereLoop n))) p
    (raw F p a ha) (raw_closed F p a ha) = a := by
  have hc := CochainClass.classOf_map (cochainCxZMod2 (TopCat.of (SphereLoop n)))
    (singularCochainComplexZMod2.map (LengthEnergyMaps.normalizer F).op) p
    (NormalizedRelativeRepresentative.raw (TopCat.of (SphereLoop n)) (energyCut F L) p a ha)
    (NormalizedRelativeRepresentative.raw_closed (TopCat.of (SphereLoop n)) (energyCut F L) p a ha)
    (raw_closed F p a ha)
  change (cohPullback (LengthEnergyMaps.normalizer F) p).hom
      (CochainClass.classOf (cochainCxZMod2 (TopCat.of (SphereLoop n))) p
        (NormalizedRelativeRepresentative.raw (TopCat.of (SphereLoop n)) (energyCut F L) p a ha)
        (NormalizedRelativeRepresentative.raw_closed (TopCat.of (SphereLoop n)) (energyCut F L) p a ha)) =
    CochainClass.classOf (cochainCxZMod2 (TopCat.of (SphereLoop n))) p (raw F p a ha)
      (raw_closed F p a ha) at hc
  rw [NormalizedRelativeRepresentative.raw_class, LengthEnergyMaps.normalizer_cohomology] at hc
  exact hc.symm

def cocycle : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p :=
  SingularNormalization.normalize (TopCat.of (SphereLoop n)) p (raw F p a ha)

theorem cocycle_closed :
    cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p (cocycle F p a ha) = 0 :=
  SingularNormalization.normalize_closed _ p (raw F p a ha) (raw_closed F p a ha)

theorem cocycle_supported (hL : 0 < L) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L)) p
      (cocycle F p a ha) = 0 :=
  SingularNormalization.normalize_supported _ p (raw F p a ha) (raw_supported F p a ha hL)

theorem cocycle_normalized :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (TopCat.of (SphereLoop n)))
      (cocycle F p a ha) := SingularNormalization.normalize_degeneracies _ p (raw F p a ha)

theorem cocycle_class (hp : 1 ≤ p) :
    CochainClass.classOf (cochainCxZMod2 (TopCat.of (SphereLoop n))) p (cocycle F p a ha)
      (cocycle_closed F p a ha) = a :=
  (SingularNormalization.normalize_class_pos _ p hp (raw F p a ha) (raw_closed F p a ha)).trans
    (raw_class F p a ha)

include ha in
theorem exists_normalized_supported (hp : 1 ≤ p) (hL : 0 < L) :
    ∃ T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p,
      ∃ hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0,
        DoldKan.DegeneraciesVanish
          (X := SingularNormalization.linearization (TopCat.of (SphereLoop n))) T ∧
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L)) p T = 0 ∧
        CochainClass.classOf (cochainCxZMod2 (TopCat.of (SphereLoop n))) p T hT = a :=
  ⟨cocycle F p a ha, cocycle_closed F p a ha, cocycle_normalized F p a ha,
    cocycle_supported F p a ha hL, cocycle_class F p a ha hp⟩

end
end Finsler.LengthSupportedCocycle
