module

public import Finsler.Loop.CloseSphereHomotopy

/-! Uniformly close actual continuous circle-loop families are
homotopic through actual sphere-valued loops. Coincident members of
the families are fixed for the entire genuine homotopy. -/

@[expose] public section
namespace Finsler.CloseContinuousLoopHomotopy
open CategoryTheory
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelEvaluation Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000
local notation "Circ" => SobolevCircleRepresentative.Circle

def evaluationMap {n : ℕ} {X : TopCat.{0}} (f : X ⟶ ContinuousLoopModel.space n) :
    TopCat.of (X × Circ) ⟶ sphere n :=
  TopCat.ofHom ⟨fun z => f z.1 z.2,
    continuous_eval.comp ((f.hom.continuous.comp continuous_fst).prodMk continuous_snd)⟩

theorem pointwise_close {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ ContinuousLoopModel.space n)
    (h : ∀ x, dist (f x) (g x) < 1) (z : X × Circ) :
    dist (evaluationMap f z) (evaluationMap g z) < 1 :=
  (ContinuousMap.dist_apply_le_dist (f := f z.1) (g := g z.1) z.2).trans_lt (h z.1)

def homotopy {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ ContinuousLoopModel.space n)
    (h : ∀ x, dist (f x) (g x) < 1) : TopCat.Homotopy f g :=
  let H := CloseSphereHomotopy.homotopy (evaluationMap f) (evaluationMap g) (pointwise_close f g h)
  { toFun z := ⟨fun c => H (z.1, (z.2, c)),
      H.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact H.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    map_zero_left x := by
      apply ContinuousMap.ext
      intro c
      exact H.map_zero_left (x, c)
    map_one_left x := by
      apply ContinuousMap.ext
      intro c
      exact H.map_one_left (x, c) }

theorem fixed {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ ContinuousLoopModel.space n)
    (h : ∀ x, dist (f x) (g x) < 1) (x : X) (hx : f x = g x) (t : ClosedInterval) :
    homotopy f g h (t, x) = f x := by
  apply ContinuousMap.ext
  intro c
  exact CloseSphereHomotopy.fixed (evaluationMap f) (evaluationMap g) (pointwise_close f g h)
    (x, c) (congrArg (fun u : ContinuousLoopModel.space n => u c) hx) t

end
end Finsler.CloseContinuousLoopHomotopy
