module

public import Finsler.Loop.SelfHomotopySweep
public import Finsler.Loop.ContinuousLoopHomologyEquivalence

/-! The ACTUAL loop-evaluation time homotopy has equal endpoints.
Its genuine singular prism raises homology degree by one. Natural
Kronecker duality constructs the actual degree-minus-one sphere
transgression, with exact pairings on ordinary and H1 loop classes. -/

@[expose] public section
namespace Finsler.ContinuousLoopSweep
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def evaluationHomotopy (n : ℕ) : TopCat.Homotopy
    (ContinuousLoopModel.evaluation n) (ContinuousLoopModel.evaluation n) where
  toFun z := z.2 (((z.1 : ℝ)) : SobolevCircleRepresentative.Circle)
  continuous_toFun := by
    exact continuous_eval.comp (continuous_snd.prodMk
      ((AddCircle.continuous_mk' 1).comp (continuous_subtype_val.comp continuous_fst)))
  map_zero_left _ := rfl
  map_one_left u := by
    change u (((1 : ℝ)) : SobolevCircleRepresentative.Circle) = u 0
    rw [AddCircle.coe_period]

def chainHomotopy (n : ℕ) : _root_.Homotopy (push (ContinuousLoopModel.evaluation n))
    (push (ContinuousLoopModel.evaluation n)) :=
  (evaluationHomotopy n).toSSet.chainComplexMap coeff

def homology (n q : ℕ) : homologyZMod2 (ContinuousLoopModel.space n) q ⟶
    homologyZMod2 (BorelEvaluation.sphere n) (q + 1) :=
  SelfHomotopySweep.homology (chainHomotopy n) q

def transgression (n q : ℕ) : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1) →ₗ[ZMod 2]
    cohomologyZMod2 (ContinuousLoopModel.space n) q :=
  (kroneckerEquiv (ContinuousLoopModel.space n) q).inv.hom.comp
    ((LinearMap.lcomp (ZMod 2) (ZMod 2) (homology n q).hom).comp
      (kroneckerMap (BorelEvaluation.sphere n) (q + 1)).hom)

theorem pairing (n q : ℕ) (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1))
    (z : homologyZMod2 (ContinuousLoopModel.space n) q) :
    (kroneckerMap (ContinuousLoopModel.space n) q).hom (transgression n q a) z =
      (kroneckerMap (BorelEvaluation.sphere n) (q + 1)).hom a ((homology n q).hom z) := by
  have h := ConcreteCategory.congr_hom (Iso.inv_hom_id (kroneckerEquiv (ContinuousLoopModel.space n) q))
    (((kroneckerMap (BorelEvaluation.sphere n) (q + 1)).hom a).comp (homology n q).hom)
  exact congrArg (fun v : homologyDualZMod2 (ContinuousLoopModel.space n) q => v z) h

def H1Transgression (n q : ℕ) : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1) →ₗ[ZMod 2]
    cohomologyZMod2 (Loops n) q :=
  (ContinuousLoopHomologyEquivalence.cohomology n q).toLinearMap.comp (transgression n q)

theorem H1_pairing (n q : ℕ) (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1))
    (z : homologyZMod2 (Loops n) q) :
    (kroneckerMap (Loops n) q).hom (H1Transgression n q a) z =
      (kroneckerMap (BorelEvaluation.sphere n) (q + 1)).hom a
        ((homology n q).hom (ContinuousLoopHomologyEquivalence.homology n q z)) := by
  change (kroneckerMap (Loops n) q).hom
    (ContinuousLoopHomologyEquivalence.cohomology n q (transgression n q a)) z = _
  rw [ContinuousLoopHomologyEquivalence.pairing, pairing]

end
end Finsler.ContinuousLoopSweep
