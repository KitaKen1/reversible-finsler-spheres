module

public import Finsler.Loop.CompactContinuousLoopHomotopyLift
public import Finsler.Loop.CompactHomologyLift
public import Finsler.Topology.Kronecker

/-! Every ACTUAL ordinary continuous-loop singular homology class
comes from genuine strong-H1 loops. Compact chain families, actual
polygon replacements and their real homotopies supply surjectivity.
The real ordinary cohomology pullback is consequently injective. -/

@[expose] public section
namespace Finsler.ContinuousLoopHomologySurjection
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem homology_surjective (n q : ℕ) : Function.Surjective
    (HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom := by
  intro z
  obtain ⟨K, y, hy⟩ := CompactHomologyLift.exists_lift (ContinuousLoopModel.space n) q z
  obtain ⟨e, H, -⟩ := CompactContinuousLoopHomotopyLift.exists_lift n K
  refine ⟨(HomologicalComplex.homologyMap (push e) q).hom y, ?_⟩
  change (HomologicalComplex.homologyMap (push e) q ≫
    HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom y = z
  rw [← HomologicalComplex.homologyMap_comp, ← push_comp]
  have hh : HomologicalComplex.homologyMap (push (e ≫ ContinuousLoopModel.inclusion n)) q =
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (ContinuousLoopModel.space n)
        (K : Set (ContinuousLoopModel.space n)))) q :=
    (H.toSSet.chainComplexMap coeff).homologyMap_eq q
  rw [hh]
  exact hy

theorem cohomology_injective (n q : ℕ) :
    Function.Injective (cohPullback (ContinuousLoopModel.inclusion n) q).hom := by
  intro a b he
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  obtain ⟨x, hx⟩ := homology_surjective n q z
  have h := congrArg
    (fun c : cohomologyZMod2 (Loops n) q => (kroneckerMap (Loops n) q).hom c x) he
  rw [kroneckerMap_naturality_apply, kroneckerMap_naturality_apply] at h
  change (kroneckerMap (ContinuousLoopModel.space n) q).hom a
      ((HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom x) =
    (kroneckerMap (ContinuousLoopModel.space n) q).hom b
      ((HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom x) at h
  rw [hx] at h
  exact h

end
end Finsler.ContinuousLoopHomologySurjection
