module

public import Finsler.Loop.ClosedLoopReparametrization

/-! Joint continuity for the ACTUAL closed-path reparametrization,
allowing the clock to depend on the loop and cut time. -/
@[expose] public section
namespace Finsler.ClosedLoopVariableClocks
open CategoryTheory Finsler.SphereGeometry Finsler.ClosedLoopReparametrization
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

local notation "I" => _root_.unitInterval

theorem continuous_warp {X : Type*} [TopologicalSpace X] :
    Continuous (fun z : clocks × ClosedPathCircle.closedMaps X => warp z.1 z.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have ht : Continuous (fun z : (clocks × ClosedPathCircle.closedMaps X) × I => z.1.1.val z.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst.fst).prodMk continuous_snd)
  have hc := continuous_eval.comp ((continuous_subtype_val.comp continuous_fst.snd).prodMk ht)
  exact hc.congr (fun _ => rfl)

theorem continuous_mixClock :
    Continuous (fun z : I × (clocks × clocks) => mixClock z.1 z.2.1 z.2.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hr : Continuous (fun z : (I × (clocks × clocks)) × I => z.1.2.1.val z.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst.snd.fst).prodMk continuous_snd)
  have hs : Continuous (fun z : (I × (clocks × clocks)) × I => z.1.2.2.val z.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst.snd.snd).prodMk continuous_snd)
  exact continuous_mix.comp (continuous_fst.fst.prodMk (hr.prodMk hs))

def family (n : ℕ) {X : TopCat.{0}} (r : X → clocks) (hr : Continuous r)
    (γ : X → ClosedPathCircle.closedMaps (Sphere n)) (hγ : Continuous γ) :
    X ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun x => ClosedPathCircle.circle (warp (r x) (γ x)),
    ClosedPathCircle.circle_continuous.comp (continuous_warp.comp (hr.prodMk hγ))⟩

def homotopy (n : ℕ) {X : TopCat.{0}} (r s : X → clocks) (hr : Continuous r) (hs : Continuous s)
    (γ : X → ClosedPathCircle.closedMaps (Sphere n)) (hγ : Continuous γ) :
    TopCat.Homotopy (family n r hr γ hγ) (family n s hs γ hγ) where
  toFun z := ClosedPathCircle.circle (warp (mixClock z.1 (r z.2) (s z.2)) (γ z.2))
  continuous_toFun := by
    have hc : Continuous (fun z : _root_.unitInterval × X => mixClock z.1 (r z.2) (s z.2)) :=
      continuous_mixClock.comp (continuous_fst.prodMk ((hr.comp continuous_snd).prodMk (hs.comp continuous_snd)))
    exact ClosedPathCircle.circle_continuous.comp
      (continuous_warp.comp (hc.prodMk (hγ.comp continuous_snd)))
  map_zero_left x := by change ClosedPathCircle.circle (warp (mixClock 0 (r x) (s x)) (γ x)) = _; rw [mixClock_zero]; rfl
  map_one_left x := by change ClosedPathCircle.circle (warp (mixClock 1 (r x) (s x)) (γ x)) = _; rw [mixClock_one]; rfl

end
end Finsler.ClosedLoopVariableClocks
