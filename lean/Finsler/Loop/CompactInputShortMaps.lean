module

public import Finsler.Loop.CompactInputLengthBudget
public import Finsler.Topology.FilteredPrismSelfCut
public import Finsler.Topology.AnnularTimeTrim

/-! Actual compact-family input maps to strict length sublevels,
with exact original cylinder, endpoint and genuine prism squares. -/

@[expose] public section
namespace Finsler.CompactInputShortMaps

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P : Type} [TopologicalSpace P] {n : ℕ}
  (α : C(P, SphereLoop n)) (F : ReversibleMetric n) (a : ℝ)
  (hA : ∀ x, SobolevLength.length F (α x) < a)

def family : TopCat.of P ⟶ TopCat.of (SelfCutOscillation.short F a) :=
  TopCat.ofHom ⟨fun x => ⟨α x, hA x⟩, α.continuous.subtype_mk _⟩

theorem family_source : family α F a hA ≫
    SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F a) = TopCat.ofHom α := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def cylinder : TopCat.of (ClosedInterval × P) ⟶ FilteredPrismSelfCut.domain F a :=
  TopCat.ofHom ⟨fun z => (z.1, family α F a hA z.2), by fun_prop⟩

theorem cylinder_source : cylinder α F a hA ≫ FilteredPrismSelfCut.forget F a = AnnularSelfCut.familyMap α := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem endpoint_square (t : ClosedInterval) :
    AnnularTimeTrim.slice (TopCat.of P) t ≫ cylinder α F a hA =
      family α F a hA ≫ FilteredPrismSelfCut.atTimeBelow F a t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem prism_square (j : ℕ) :
    (push (family α F a hA)).f j ≫
      ((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom j (j + 1) =
    AnnularTimeTrim.prism (TopCat.of P) j ≫ (push (cylinder α F a hA)).f (j + 1) := by
  rw [TimePrismNaturality.prism_pre, AnnularTimeTrim.prism, TimePrismNaturality.prism_post]
  apply TimePrismNaturality.prism_congr
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

end
end Finsler.CompactInputShortMaps
