module

public import Finsler.Topology.CupOne
public import Finsler.Topology.SupportedCapNaturality
public import Finsler.Analysis.SelfCutOscillation

/-! Use actual cup-one naturality to retain tested-length support.
This covers the entire acyclic-model primitive, so no particular
block/skip face expansion or global cocycle assumption is required. -/

@[expose] public section
namespace Finsler.TestedCupOneSupport

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {X : TopCat.{0}} {n : ℕ} (F : ReversibleMetric n)
  (tested : X ⟶ TopCat.of (SphereLoop n)) (L : ℝ) (k p : ℕ)
  (φ : singularCochainGroup (ZMod 2) X k)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
    (SelfCutOscillation.short F L)) p T = 0)

-- Keep the short-domain map explicit to fix every topology and universe.
def short : Set X := {z | SobolevLength.length F (tested z) < L}

include hshort in
theorem tested_zero :
    cochainPullback (SupportedCap.subspaceMap X (short F tested L)) p
      (cochainPullback tested p T) = 0 :=
  pullback_support tested (short F tested L) (SelfCutOscillation.short F L)
    (fun _ hz => hz) p T hshort

include hshort in
theorem gamma_zero :
    cochainPullback (SupportedCap.subspaceMap X (short F tested L)) (k + p)
      (cochainCup k p φ (cochainPullback tested p T)) = 0 := by
  rw [cochainCup_naturality, tested_zero F tested L p T hshort, cochainCup_zero_right]

include hshort in
theorem primitive_zero (a d : ℕ) (h : a + (k + p) = d + 1)
    (σ : singularCochainGroup (ZMod 2) X a) :
    cochainPullback (SupportedCap.subspaceMap X (short F tested L)) d
      (CupOne.cupOne X a (k + p) d h σ (cochainCup k p φ (cochainPullback tested p T))) = 0 :=
  CupOne.restriction_zero (SupportedCap.subspaceMap X (short F tested L)) a (k + p) d h σ _
    (Or.inr (gamma_zero F tested L k p φ T hshort))

theorem coboundary_zero (d : ℕ) (ξ : singularCochainGroup (ZMod 2) X d)
    (hξ : cochainPullback (SupportedCap.subspaceMap X (short F tested L)) d ξ = 0) :
    cochainPullback (SupportedCap.subspaceMap X (short F tested L)) (d + 1)
      (cochainCoboundary (ZMod 2) X d ξ) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X (short F tested L)).op).comm d (d + 1)) ξ
  change cochainCoboundary (ZMod 2) (TopCat.of (short F tested L)) d
    (cochainPullback (SupportedCap.subspaceMap X (short F tested L)) d ξ) = _ at he
  rw [hξ] at he
  exact he.symm.trans (map_zero _)

include hshort in
theorem primitive_boundary_zero (a d : ℕ) (h : a + (k + p) = d + 1)
    (σ : singularCochainGroup (ZMod 2) X a) :
    cochainPullback (SupportedCap.subspaceMap X (short F tested L)) (d + 1)
      (cochainCoboundary (ZMod 2) X d
        (CupOne.cupOne X a (k + p) d h σ (cochainCup k p φ (cochainPullback tested p T)))) = 0 :=
  coboundary_zero F tested L d _ (primitive_zero F tested L k p φ T hshort a d h σ)

end
end Finsler.TestedCupOneSupport
