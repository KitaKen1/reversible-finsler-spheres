module

public import Finsler.Loop.H1LoopHomologyInjection

/-! Actual every-degree homology and cohomology equivalences for the
genuine H1-to-ordinary loop inclusion. Both bundled equivalences have
the original induced maps as their forward maps. -/

@[expose] public section
namespace Finsler.ContinuousLoopHomologyEquivalence
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def homology (n q : ℕ) : (chains (Loops n)).homology q ≃ₗ[ZMod 2]
    (chains (ContinuousLoopModel.space n)).homology q :=
  LinearEquiv.ofBijective
    (HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom
    ⟨H1LoopHomologyInjection.homology_injective n q,
      ContinuousLoopHomologySurjection.homology_surjective n q⟩

theorem homology_apply (n q : ℕ) (z : (chains (Loops n)).homology q) :
    homology n q z =
      (HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q).hom z := rfl

theorem cohomology_surjective (n q : ℕ) :
    Function.Surjective (cohPullback (ContinuousLoopModel.inclusion n) q).hom := by
  intro a
  let φ : homologyZMod2 (ContinuousLoopModel.space n) q →ₗ[ZMod 2] ZMod 2 :=
    ((kroneckerMap (Loops n) q).hom a).comp (homology n q).symm.toLinearMap
  obtain ⟨b, hb⟩ := kroneckerMap_surjective (ContinuousLoopModel.space n) q φ
  refine ⟨b, ?_⟩
  apply kroneckerMap_injective
  rw [kroneckerMap_naturality_apply, hb]
  apply LinearMap.ext
  intro x
  change ((kroneckerMap (Loops n) q).hom a)
    ((homology n q).symm ((homology n q) x)) = _
  rw [LinearEquiv.symm_apply_apply]

def cohomology (n q : ℕ) : cohomologyZMod2 (ContinuousLoopModel.space n) q ≃ₗ[ZMod 2]
    cohomologyZMod2 (Loops n) q :=
  LinearEquiv.ofBijective (cohPullback (ContinuousLoopModel.inclusion n) q).hom
    ⟨ContinuousLoopHomologySurjection.cohomology_injective n q, cohomology_surjective n q⟩

theorem cohomology_apply (n q : ℕ) (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    cohomology n q a = (cohPullback (ContinuousLoopModel.inclusion n) q).hom a := rfl

theorem pairing (n q : ℕ) (a : cohomologyZMod2 (ContinuousLoopModel.space n) q)
    (z : (chains (Loops n)).homology q) :
    (kroneckerMap (Loops n) q).hom (cohomology n q a) z =
      (kroneckerMap (ContinuousLoopModel.space n) q).hom a (homology n q z) := by
  exact congrArg (fun φ => φ z)
    (kroneckerMap_naturality_apply (ContinuousLoopModel.inclusion n) q a)

end
end Finsler.ContinuousLoopHomologyEquivalence
