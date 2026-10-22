module

public import Finsler.Loop.MeridianInteriorDirection

/-! Exact self-coincidence loci for the actual variable quarters.
Same-side interior coincidences are parameter/time diagonals;
opposite-side coincidences are precisely the equator seam. -/
@[expose] public section
namespace Finsler.MeridianQuarterIncidence
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.RationalSphereArc
open Finsler.RationalSphereArcCoordinates Finsler.MeridianInteriorDirection
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def northTime (t : _root_.unitInterval) : _root_.unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
def southTime (t : _root_.unitInterval) : _root_.unitInterval :=
  ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

theorem north_meridian {n : ℕ} (P : Sphere n) (v : equator P) (t : _root_.unitInterval) :
    meridian P v (northTime t) = point (outgoing P v) t := by
  calc
    _ = (meridian P v).extend ((t : ℝ) / 2) := (Path.extend_apply _ (northTime t).property).symm
    _ = _ := by
      rw [meridian, Path.extend_trans_of_le_half _ _ (by linarith [t.property.2]),
        show 2 * ((t : ℝ) / 2) = (t : ℝ) by ring]
      exact Path.extend_apply _ t.property

theorem south_meridian {n : ℕ} (P : Sphere n) (v : equator P) (t : _root_.unitInterval) :
    meridian P v (southTime t) = point (incoming P v) t := by
  calc
    _ = (meridian P v).extend ((1 + (t : ℝ)) / 2) := (Path.extend_apply _ (southTime t).property).symm
    _ = _ := by
      rw [meridian, Path.extend_trans_of_half_le _ _ (by linarith [t.property.1]),
        show 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ) by ring]
      exact Path.extend_apply _ t.property

theorem north_north_iff {n : ℕ} (P : Sphere n) (v w : equator P)
    (s t : _root_.unitInterval) (hs : 0 < (s : ℝ)) (ht : 0 < (t : ℝ)) :
    point (outgoing P v) s = point (outgoing P w) t ↔ v = w ∧ s = t := by
  constructor
  · intro h
    have hv : v = w := coincidence_direction P v w (northTime s) (northTime t)
      (by dsimp [northTime]; linarith) (by dsimp [northTime]; linarith [s.property.2])
      (by dsimp [northTime]; linarith) (by dsimp [northTime]; linarith [t.property.2])
      (by rw [north_meridian, north_meridian]; exact h)
    refine ⟨hv, ?_⟩
    rw [hv] at h
    exact point_injective (outgoing P w) h
  · rintro ⟨rfl, rfl⟩; rfl

theorem south_south_iff {n : ℕ} (P : Sphere n) (v w : equator P)
    (s t : _root_.unitInterval) (hs : (s : ℝ) < 1) (ht : (t : ℝ) < 1) :
    point (incoming P v) s = point (incoming P w) t ↔ v = w ∧ s = t := by
  constructor
  · intro h
    have hv : v = w := coincidence_direction P v w (southTime s) (southTime t)
      (by dsimp [southTime]; linarith [s.property.1]) (by dsimp [southTime]; linarith)
      (by dsimp [southTime]; linarith [t.property.1]) (by dsimp [southTime]; linarith)
      (by rw [south_meridian, south_meridian]; exact h)
    refine ⟨hv, ?_⟩
    rw [hv] at h
    exact point_injective (incoming P w) h
  · rintro ⟨rfl, rfl⟩; rfl

theorem north_south_iff {n : ℕ} (P : Sphere n) (v w : equator P) (s t : _root_.unitInterval) :
    point (outgoing P v) s = point (incoming P w) t ↔ s = 1 ∧ t = 0 ∧ v = w := by
  have hn : ⟪(P : Ambient n), (point (outgoing P v) s : Ambient n)⟫ = alpha s :=
    RationalSphereArcCarrier.inner_left (outgoing P v) s
  have hs : ⟪(P : Ambient n), (point (incoming P w) t : Ambient n)⟫ = -beta t := by
    have h := RationalSphereArcCarrier.inner_right (incoming P w) t
    change ⟪-(P : Ambient n), (point (incoming P w) t : Ambient n)⟫ = beta t at h
    rw [inner_neg_left] at h
    linarith
  constructor
  · intro h
    have he := congrArg (fun x : Sphere n => ⟪(P : Ambient n), (x : Ambient n)⟫) h
    have hc : alpha s = -beta t := hn.symm.trans (he.trans hs)
    have ha : alpha s = 0 := by linarith [alpha_nonneg s, beta_nonneg t]
    have hb : beta t = 0 := by linarith
    have h₁ := (alpha_zero_iff s).mp ha
    have h₀ := (beta_zero_iff t).mp hb
    refine ⟨h₁, h₀, ?_⟩
    apply Subtype.ext
    simpa only [h₁, h₀, point_one, point_zero, outgoing, incoming] using h
  · rintro ⟨rfl, rfl, rfl⟩
    rw [point_one, point_zero]
    rfl

end
end Finsler.MeridianQuarterIncidence
