module

public import Finsler.Loop.DegreeLoweringCohomologyPullback
public import Finsler.Topology.SupportedCapNaturality

/-! The induced degree-lowering cohomology operation respects ACTUAL
continuous input and output maps. Proofs use the real Kronecker
pairing and naturality, without postulated duality squares. -/

@[expose] public section
namespace Finsler.DegreeLoweringCohomologyNaturality
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

theorem post {X Y Z : TopCat.{0}} {d : ℕ}
    (f : DegreeLoweringHomology.Map (chainCxZMod2 X) (chainCxZMod2 Y) d)
    (e : Y ⟶ Z) (q : ℕ) (a : cohomologyZMod2 Z q) :
    DegreeLoweringCohomologyPullback.map (f.post (push e)) q a =
      DegreeLoweringCohomologyPullback.map f q ((cohPullback e q).hom a) := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  rw [DegreeLoweringCohomologyPullback.pairing, DegreeLoweringHomology.Map.post_homology,
    DegreeLoweringCohomologyPullback.pairing, kroneckerMap_naturality_apply]
  rfl

theorem pre {W X Y : TopCat.{0}} {d : ℕ}
    (f : DegreeLoweringHomology.Map (chainCxZMod2 X) (chainCxZMod2 Y) d)
    (e : W ⟶ X) (q : ℕ) (a : cohomologyZMod2 Y q) :
    DegreeLoweringCohomologyPullback.map (f.pre (push e)) q a =
      (cohPullback e (d + q)).hom (DegreeLoweringCohomologyPullback.map f q a) := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  rw [DegreeLoweringCohomologyPullback.pairing, DegreeLoweringHomology.Map.pre_homology,
    kroneckerMap_naturality_apply]
  change (kroneckerMap Y q).hom a
    ((f.homology q).hom ((homologyPushZMod2 e (d + q)).hom z)) =
    (kroneckerMap X (d + q)).hom (DegreeLoweringCohomologyPullback.map f q a)
      ((homologyPushZMod2 e (d + q)).hom z)
  exact (DegreeLoweringCohomologyPullback.pairing f q a ((homologyPushZMod2 e (d + q)).hom z)).symm

end
end Finsler.DegreeLoweringCohomologyNaturality
