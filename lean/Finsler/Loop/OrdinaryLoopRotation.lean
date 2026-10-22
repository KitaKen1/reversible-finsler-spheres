module

public import Finsler.Loop.SelfHomotopySweepNaturality
public import Finsler.Loop.ContinuousLoopSweep

/-! The actual full-period rotation self-homotopy of the identity
on ordinary circle loops. Its genuine BV degree+1 map evaluates to
the ORIGINAL sphere sweep. -/
@[expose] public section
namespace Finsler.OrdinaryLoopRotation
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
local notation "Circ" => SobolevCircleRepresentative.Circle

def rotate (n : ℕ) (a : Circ) (u : ContinuousLoopModel.space n) : ContinuousLoopModel.space n :=
  ⟨fun x => u (a + x), u.continuous.comp (continuous_const.add continuous_id)⟩

theorem joint_continuous (n : ℕ) :
    Continuous (fun z : ContinuousLoopModel.space n × Circ => rotate n z.2 z.1) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ContinuousLoopModel.space n × Circ) × Circ => z.1.1 (z.1.2 + z.2))
  fun_prop

theorem rotate_zero (n : ℕ) (u : ContinuousLoopModel.space n) : rotate n 0 u = u := by
  apply ContinuousMap.ext
  intro x
  change u (0 + x) = u x
  rw [zero_add]

theorem rotate_add (n : ℕ) (a b : Circ) (u : ContinuousLoopModel.space n) :
    rotate n a (rotate n b u) = rotate n (a + b) u := by
  apply ContinuousMap.ext
  intro x
  change u (b + (a + x)) = u ((a + b) + x)
  congr 1
  ac_rfl

def homotopy (n : ℕ) : TopCat.Homotopy (𝟙 (ContinuousLoopModel.space n)) (𝟙 (ContinuousLoopModel.space n)) where
  toFun z := rotate n ((z.1 : ℝ) : Circ) z.2
  continuous_toFun := (joint_continuous n).comp
    (continuous_snd.prodMk ((AddCircle.continuous_mk' 1).comp
      (continuous_subtype_val.comp continuous_fst)))
  map_zero_left u := rotate_zero n u
  map_one_left u := by
    change rotate n ((1 : ℝ) : Circ) u = u
    rw [AddCircle.coe_period, rotate_zero]

def chainHomotopy (n : ℕ) := (homotopy n).toSSet.chainComplexMap coeff

def BV (n q : ℕ) : homologyZMod2 (ContinuousLoopModel.space n) q ⟶
    homologyZMod2 (ContinuousLoopModel.space n) (q + 1) :=
  SelfHomotopySweep.homology (chainHomotopy n) q

theorem prism_evaluation (n q : ℕ) :
    (chainHomotopy n).hom q (q + 1) ≫ (push (ContinuousLoopModel.evaluation n)).f (q + 1) =
      (ContinuousLoopSweep.chainHomotopy n).hom q (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (ContinuousLoopModel.evaluation n)) (homotopy n)).h =
      (ContinuousLoopSweep.evaluationHomotopy n).h := by
    ext z : 1
    let t : _root_.unitInterval := z.2.down
    change z.1 (((t : ℝ) : Circ) + 0) = z.1 ((t : ℝ) : Circ)
    rw [add_zero]
  exact (TimePrismNaturality.prism_post (homotopy n) (ContinuousLoopModel.evaluation n) q).trans
    (TimePrismNaturality.prism_congr _ _ he q)

theorem BV_evaluation (n q : ℕ) :
    BV n q ≫ HomologicalComplex.homologyMap (push (ContinuousLoopModel.evaluation n)) (q + 1) =
      ContinuousLoopSweep.homology n q := by
  have h := SelfHomotopySweepNaturality.homology (chainHomotopy n)
    (ContinuousLoopSweep.chainHomotopy n) (𝟙 _) (push (ContinuousLoopModel.evaluation n))
    (fun q => by rw [HomologicalComplex.id_f, Category.id_comp]; exact (prism_evaluation n q).symm) q
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at h
  exact h.symm

end
end Finsler.OrdinaryLoopRotation
