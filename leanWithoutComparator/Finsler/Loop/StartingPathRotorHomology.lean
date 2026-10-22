module

public import Finsler.Loop.StartingPathOverlapChart
public import Finsler.Loop.ProductFiberGeneration

/-! Retain the ACTUAL maps from one fixed-end fiber into BOTH
starting-path patches and the actual overlap. The two patch maps
are homology-injective in every degree. Actual product fiber
generation gives generation of the actual overlap. -/
@[expose] public section
namespace Finsler.StartingPathRotorHomology
open CategoryTheory AlgebraicTopology SphereOddDegree Topology
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.H1PuncturedEvaluationChart Finsler.StartingPathSphereCover
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

def alignment {n : ℕ} (x a : Sphere n) : patch x a ⟶ TopCat.of (Path x a) :=
  TopCat.ofHom ⟨StartingPathRotorChart.forwardPath x a,
    continuous_snd.comp (StartingPathRotorChart.homeomorph x a).continuous⟩

theorem north_square {n : ℕ} (x a z : Sphere n) (hz : z ∈ base a ∩ base (antipode a)) :
    (fiberToOverlap x a z hz ≫ north x a) ≫ alignment x a =
      (TopCat.isoOfHomeo (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨z, hz.1⟩)).hom := by
  ext p : 1
  apply Path.ext
  funext t
  change TimedRotorPunctured.sphereMap (RotorHomotopy.path t (p 1 : Ambient n) (a : Ambient n)) (p t) =
    TimedRotorPunctured.sphereMap (RotorHomotopy.path t (z : Ambient n) (a : Ambient n)) (p t)
  rw [p.target]

theorem south_square {n : ℕ} (x a z : Sphere n) (hz : z ∈ base a ∩ base (antipode a)) :
    (fiberToOverlap x a z hz ≫ south x a) ≫ alignment x (antipode a) =
      (TopCat.isoOfHomeo (StartingPathRotorChart.fixedFiberHomeomorph x (antipode a) ⟨z, hz.2⟩)).hom := by
  ext p : 1
  apply Path.ext
  funext t
  change TimedRotorPunctured.sphereMap (RotorHomotopy.path t (p 1 : Ambient n) (antipode a : Ambient n)) (p t) =
    TimedRotorPunctured.sphereMap (RotorHomotopy.path t (z : Ambient n) (antipode a : Ambient n)) (p t)
  rw [p.target]

theorem north_injective {n : ℕ} (x a z : Sphere n) (hz : z ∈ base a ∩ base (antipode a)) (k : ℕ) :
    Function.Injective (homologyPushZMod2 (fiberToOverlap x a z hz ≫ north x a) k).hom := by
  let e := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Path x z)) (Y := TopCat.of (Path x a))
      (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨z, hz.1⟩))
  intro u v huv
  apply e.toLinearEquiv.injective
  have he := congrArg (homologyPushZMod2 (alignment x a) k).hom huv
  rw [SplitPairHomologyKernel.push_comp_apply, SplitPairHomologyKernel.push_comp_apply, north_square] at he
  exact he

theorem south_injective {n : ℕ} (x a z : Sphere n) (hz : z ∈ base a ∩ base (antipode a)) (k : ℕ) :
    Function.Injective (homologyPushZMod2 (fiberToOverlap x a z hz ≫ south x a) k).hom := by
  let e := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Path x z)) (Y := TopCat.of (Path x (antipode a)))
      (StartingPathRotorChart.fixedFiberHomeomorph x (antipode a) ⟨z, hz.2⟩))
  intro u v huv
  apply e.toLinearEquiv.injective
  have he := congrArg (homologyPushZMod2 (alignment x (antipode a)) k).hom huv
  rw [SplitPairHomologyKernel.push_comp_apply, SplitPairHomologyKernel.push_comp_apply, south_square] at he
  exact he

theorem fiber_surjective_of_section {n : ℕ} (x a z : Sphere n)
    (hz : z ∈ base a ∩ base (antipode a)) (k : ℕ)
    (hs : Function.Surjective (homologyPushZMod2
      (ProductHomologyDetectionTransport.fiberSection (NativeEvaluationMayerVietoris.baseOverlap a)
        (TopCat.of (Path x a)) ⟨z, hz⟩) k).hom) :
    Function.Surjective (homologyPushZMod2 (fiberToOverlap x a z hz) k).hom := by
  let e := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (StartingPathOverlapChart.iso x a)
  let f := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Path x z)) (Y := TopCat.of (Path x a))
      (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨z, hz.1⟩))
  intro w
  obtain ⟨u, hu⟩ := hs (e.toLinearEquiv w)
  refine ⟨f.toLinearEquiv.symm u, ?_⟩
  apply e.toLinearEquiv.injective
  change (homologyPushZMod2 (StartingPathOverlapChart.iso x a).hom k).hom
    ((homologyPushZMod2 (fiberToOverlap x a z hz) k).hom (f.toLinearEquiv.symm u)) = e.toLinearEquiv w
  rw [SplitPairHomologyKernel.push_comp_apply, StartingPathOverlapChart.fixed_fiber_square,
    ← SplitPairHomologyKernel.push_comp_apply]
  change (homologyPushZMod2 (ProductHomologyDetectionTransport.fiberSection
    (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) ⟨z, hz⟩) k).hom
      (f.toLinearEquiv (f.toLinearEquiv.symm u)) = e.toLinearEquiv w
  rw [LinearEquiv.apply_symm_apply]
  exact hu

end
end Finsler.StartingPathRotorHomology
