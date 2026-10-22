module

public import Finsler.Loop.ClosedPathCircle
public import Finsler.Loop.ContinuousLoopSweep

/-! Endpoint-preserving interval reparametrizations give actual ordinary
loop homotopies, including front/back pauses. All source endpoints and
circle seams are retained; no H1 differentiability of the homotopy is assumed. -/
@[expose] public section
namespace Finsler.ClosedLoopReparametrization
open CategoryTheory Finsler.SphereGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

local notation "I" => _root_.unitInterval
abbrev clocks := {r : C(I, I) // r 0 = 0 ∧ r 1 = 1}

def early : clocks :=
  ⟨⟨fun t => ⟨min (2 * (t : ℝ)) 1, by
      constructor
      · exact le_min (by linarith [t.property.1]) zero_le_one
      · exact min_le_right _ _⟩,
    (by fun_prop)⟩, by constructor <;> apply Subtype.ext <;> norm_num⟩

def late : clocks :=
  ⟨⟨fun t => ⟨max (2 * (t : ℝ) - 1) 0, by
      constructor
      · exact le_max_right _ _
      · exact max_le (by linarith [t.property.2]) zero_le_one⟩,
    (by fun_prop)⟩, by constructor <;> apply Subtype.ext <;> norm_num⟩

def identity : clocks := ⟨ContinuousMap.id I, rfl, rfl⟩

def mix (a r s : I) : I :=
  ⟨(1 - (a : ℝ)) * r + (a : ℝ) * s, by
    constructor
    · exact add_nonneg (mul_nonneg (by linarith [a.property.2]) r.property.1)
        (mul_nonneg a.property.1 s.property.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr a.property.2) (sub_nonneg.mpr r.property.2),
        mul_nonneg a.property.1 (sub_nonneg.mpr s.property.2)]⟩

theorem continuous_mix : Continuous (fun z : I × (I × I) => mix z.1 z.2.1 z.2.2) := by
  unfold mix
  fun_prop

def mixClock (a : I) (r s : clocks) : clocks :=
  ⟨⟨fun t => mix a (r.val t) (s.val t),
    continuous_mix.comp (continuous_const.prodMk (r.val.continuous.prodMk s.val.continuous))⟩, by
    constructor
    · apply Subtype.ext
      change (1 - (a : ℝ)) * (r.val 0 : ℝ) + (a : ℝ) * (s.val 0 : ℝ) = 0
      simp only [r.property.1, s.property.1, Set.Icc.coe_zero, mul_zero, add_zero]
    · apply Subtype.ext
      change (1 - (a : ℝ)) * (r.val 1 : ℝ) + (a : ℝ) * (s.val 1 : ℝ) = 1
      simp only [r.property.2, s.property.2, Set.Icc.coe_one, mul_one]
      ring⟩

theorem mixClock_zero (r s : clocks) : mixClock 0 r s = r := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  simp [mixClock, mix]

theorem mixClock_one (r s : clocks) : mixClock 1 r s = s := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  simp [mixClock, mix]

def warp {X : Type*} [TopologicalSpace X] (r : clocks) (γ : ClosedPathCircle.closedMaps X) :
    ClosedPathCircle.closedMaps X :=
  ⟨γ.val.comp r.val, by simpa only [ContinuousMap.comp_apply, r.property.1, r.property.2] using γ.property⟩

theorem warp_identity {X : Type*} [TopologicalSpace X] (γ : ClosedPathCircle.closedMaps X) :
    warp identity γ = γ := by
  apply Subtype.ext
  rfl

theorem continuous_mixed_warp {X : Type*} [TopologicalSpace X] (r s : clocks) :
    Continuous (fun z : I × ClosedPathCircle.closedMaps X => warp (mixClock z.1 r s) z.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have ht : Continuous (fun z : (I × ClosedPathCircle.closedMaps X) × I =>
      mix z.1.1 (r.val z.2) (s.val z.2)) :=
    continuous_mix.comp ((continuous_fst.fst).prodMk
      ((r.val.continuous.comp continuous_snd).prodMk (s.val.continuous.comp continuous_snd)))
  have hc := continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst.snd).prodMk ht)
  exact hc.congr (fun _ => rfl)

def circleMap (n : ℕ) (r : clocks) : TopCat.of (ClosedPathCircle.closedMaps (Sphere n)) ⟶
    ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun γ => ClosedPathCircle.circle (warp r γ), by
    have hi : Continuous (fun γ : ClosedPathCircle.closedMaps (Sphere n) => ((0 : I), γ)) :=
      continuous_const.prodMk continuous_id
    have hc := (continuous_mixed_warp r r).comp hi
    have he : ∀ γ : ClosedPathCircle.closedMaps (Sphere n), warp (mixClock 0 r r) γ = warp r γ := by
      intro γ
      rw [mixClock_zero]
    exact ClosedPathCircle.circle_continuous.comp (hc.congr he)⟩

def homotopy (n : ℕ) (r s : clocks) : TopCat.Homotopy (circleMap n r) (circleMap n s) where
  toFun z := ClosedPathCircle.circle (warp (mixClock z.1 r s) z.2)
  continuous_toFun := ClosedPathCircle.circle_continuous.comp (continuous_mixed_warp r s)
  map_zero_left γ := by change ClosedPathCircle.circle (warp (mixClock 0 r s) γ) = _; rw [mixClock_zero]; rfl
  map_one_left γ := by change ClosedPathCircle.circle (warp (mixClock 1 r s) γ) = _; rw [mixClock_one]; rfl

theorem homology_eq (n : ℕ) (r s : clocks) (q : ℕ) :
    SphereOddDegree.homologyPushZMod2 (circleMap n r) q =
      SphereOddDegree.homologyPushZMod2 (circleMap n s) q :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (homotopy n r s) _ q

end
end Finsler.ClosedLoopReparametrization
