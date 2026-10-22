module

public import Finsler.Geometry.LoopEnergy

/-! A variational closed-geodesic specification, with actual smooth variations
and the actual integral energy. Stationarity requires HasDerivAt, so a junk
value of deriv cannot satisfy the condition. SphereCoordinateEuler proves
comparison with the actual coordinate equation for regular smooth loops;
H¹ critical-point regularity remains separate. -/

@[expose] public section

namespace Finsler.Geodesics

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops TauCeti.Manifold Function
open scoped Manifold ContDiff

noncomputable section

structure SmoothVariation (n : ℕ) where
  family : ℝ × ℝ → Sphere n
  smooth : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ family
  periodic : ∀ s : ℝ, Periodic (fun t => family (s, t)) 1

variable {n : ℕ}

def loopAt (V : SmoothVariation n) (s : ℝ) : SmoothLoop n where
  curve := fun t => V.family (s, t)
  smooth := V.smooth.comp (contDiff_const.prodMk contDiff_id).contMDiff
  periodic := V.periodic s

def constantVariation (γ : SmoothLoop n) : SmoothVariation n where
  family := fun p => γ p.2
  smooth := γ.smooth.comp contDiff_snd.contMDiff
  periodic := fun _ => γ.periodic

theorem loopAt_constantVariation (γ : SmoothLoop n) (s : ℝ) :
    loopAt (constantVariation γ) s = γ := by
  ext t
  rfl

def Regular (γ : SmoothLoop n) : Prop := ∀ t, curveVelocity (𝓡 n) γ t ≠ 0

theorem regular_nonconstant {γ : SmoothLoop n} (hγ : Regular γ) : Nonconstant γ := by
  by_contra h
  have he : (γ : ℝ → Sphere n) = (fun _ => γ 0) := by
    funext t
    by_contra ht
    exact h ⟨t, 0, ht⟩
  have hz := hγ 0
  rw [he, curveVelocity_const] at hz
  exact hz rfl

theorem regular_energy_pos (F : ReversibleMetric n) (γ : SmoothLoop n) (hγ : Regular γ) :
    0 < Finsler.LoopEnergy.energy F γ := by
  apply intervalIntegral.integral_pos (by norm_num)
    (Finsler.LoopEnergy.density_continuous F γ).continuousOn
    (fun _ _ => sq_nonneg _)
  refine ⟨0, by norm_num, ?_⟩
  change 0 < F.value (curveVelocityLift (𝓡 n) γ 0) ^ 2
  rw [curveVelocityLift_apply]
  exact sq_pos_of_pos (F.positive (γ 0) _ (hγ 0))

/-- Zero first variation of the actual energy under every smooth periodic family. -/
def Stationary (F : ReversibleMetric n) (γ : SmoothLoop n) : Prop :=
  ∀ V : SmoothVariation n, loopAt V 0 = γ →
    HasDerivAt (fun s => Finsler.LoopEnergy.energy F (loopAt V s)) 0 0

/-- Closed geodesic in the variational formulation. The comparison with the
actual coordinate equation is proved separately in SphereCoordinateEuler. -/
structure ClosedGeodesic (F : ReversibleMetric n) where
  loop : SmoothLoop n
  regular : Regular loop
  stationary : Stationary F loop

theorem closedGeodesic_nonconstant {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    Nonconstant γ.loop := regular_nonconstant γ.regular

theorem regular_reverse {γ : SmoothLoop n} (hγ : Regular γ) : Regular (reverse γ) := by
  intro t
  have hvel := curveVelocity_comp (I := 𝓡 n) (hasDerivAt_id t).neg
    (γ.smooth.mdifferentiableAt (by simp))
  have he : curveVelocity (𝓡 n) (reverse γ) t = -curveVelocity (𝓡 n) γ (-t) := by
    simpa [reverse, comp_def] using hvel
  rw [he]
  exact neg_ne_zero.mpr (hγ (-t))

def reverseVariation (V : SmoothVariation n) : SmoothVariation n where
  family := fun p => V.family (p.1, -p.2)
  smooth := V.smooth.comp (contDiff_fst.prodMk contDiff_snd.neg).contMDiff
  periodic := by
    intro s t
    change V.family (s, -(t + 1)) = V.family (s, -t)
    simpa only [neg_add] using (V.periodic s).neg (-t)

theorem loopAt_reverseVariation (V : SmoothVariation n) (s : ℝ) :
    loopAt (reverseVariation V) s = reverse (loopAt V s) := by
  apply loop_ext
  intro t
  rfl

theorem stationary_reverse {F : ReversibleMetric n} {γ : SmoothLoop n}
    (hγ : Stationary F γ) : Stationary F (reverse γ) := by
  intro V hV
  have hbase : loopAt (reverseVariation V) 0 = γ := by
    rw [loopAt_reverseVariation, hV, reverse_reverse]
  have h := hγ (reverseVariation V) hbase
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
    change Finsler.LoopEnergy.energy F (loopAt V s) =
      Finsler.LoopEnergy.energy F (loopAt (reverseVariation V) s)
    rw [loopAt_reverseVariation, Finsler.LoopEnergy.energy_reverse])

def reverseGeodesic {F : ReversibleMetric n} (γ : ClosedGeodesic F) : ClosedGeodesic F where
  loop := reverse γ.loop
  regular := regular_reverse γ.regular
  stationary := stationary_reverse γ.stationary

theorem reverseGeodesic_image {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    image (reverseGeodesic γ).loop = image γ.loop := image_reverse γ.loop

def Prime {F : ReversibleMetric n} (γ : ClosedGeodesic F) : Prop := Primitive γ.loop

theorem prime_reverseGeodesic_iff {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    Prime (reverseGeodesic γ) ↔ Prime γ := primitive_reverse_iff γ.loop

def primeImages (F : ReversibleMetric n) : Set (Set (Sphere n)) :=
  {s | ∃ γ : ClosedGeodesic F, Prime γ ∧ image γ.loop = s}

theorem prime_image_mem {F : ReversibleMetric n} (γ : ClosedGeodesic F) (hγ : Prime γ) :
    image γ.loop ∈ primeImages F := ⟨γ, hγ, rfl⟩

def InfinitePrimeImages (F : ReversibleMetric n) : Prop := (primeImages F).Infinite

/-- Candidate statement using the explicit variational definition above.
This is a proposition, not a proved theorem. OrdinaryGeodesic proves the
statement comparison; the actual infinitude proof remains open. -/
def ReversibleSphereAssertion : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ F : ReversibleMetric n, InfinitePrimeImages F

end

end Finsler.Geodesics
