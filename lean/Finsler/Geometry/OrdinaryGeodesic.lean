module

public import Finsler.Geometry.SphereCoordinateEuler
public import Finsler.Geometry.PrimeRepresentative

/-! Ordinary regular smooth closed geodesics, defined by the actual local
Euler--Lagrange equation of F² in every sphere chart. The conversions below
preserve the loop itself, hence also its least period and its image. They do
not assert regularity of H¹ critical points or infinitude of geodesics. -/

@[expose] public section

namespace Finsler.OrdinaryGeodesics

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops
open Finsler.SphereCoordinateEuler

noncomputable section

variable {n : ℕ}

structure ClosedGeodesic (F : ReversibleMetric n) where
  loop : SmoothLoop n
  regular : Finsler.Geodesics.Regular loop
  coordinateEuler : CoordinateEuler F loop

def toOrdinary {F : ReversibleMetric n} (γ : Finsler.Geodesics.ClosedGeodesic F) :
    ClosedGeodesic F where
  loop := γ.loop
  regular := γ.regular
  coordinateEuler := (stationary_iff_coordinateEuler F γ.regular).mp γ.stationary

def toVariational {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    Finsler.Geodesics.ClosedGeodesic F where
  loop := γ.loop
  regular := γ.regular
  stationary := (stationary_iff_coordinateEuler F γ.regular).mpr γ.coordinateEuler

theorem toOrdinary_loop {F : ReversibleMetric n} (γ : Finsler.Geodesics.ClosedGeodesic F) :
    (toOrdinary γ).loop = γ.loop := rfl

theorem toVariational_loop {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    (toVariational γ).loop = γ.loop := rfl

theorem toVariational_toOrdinary {F : ReversibleMetric n}
    (γ : Finsler.Geodesics.ClosedGeodesic F) : toVariational (toOrdinary γ) = γ := by
  cases γ
  rfl

theorem toOrdinary_toVariational {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    toOrdinary (toVariational γ) = γ := by
  cases γ
  rfl

def geodesicEquiv (F : ReversibleMetric n) :
    Finsler.Geodesics.ClosedGeodesic F ≃ ClosedGeodesic F where
  toFun := toOrdinary
  invFun := toVariational
  left_inv := toVariational_toOrdinary
  right_inv := toOrdinary_toVariational

def Prime {F : ReversibleMetric n} (γ : ClosedGeodesic F) : Prop := Primitive γ.loop

theorem prime_toOrdinary_iff {F : ReversibleMetric n}
    (γ : Finsler.Geodesics.ClosedGeodesic F) : Prime (toOrdinary γ) ↔ Finsler.Geodesics.Prime γ :=
  Iff.rfl

theorem prime_toVariational_iff {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    Finsler.Geodesics.Prime (toVariational γ) ↔ Prime γ := Iff.rfl

def primeImages (F : ReversibleMetric n) : Set (Set (Sphere n)) :=
  {s | ∃ γ : ClosedGeodesic F, Prime γ ∧ image γ.loop = s}

theorem variational_primeImages_eq (F : ReversibleMetric n) :
    Finsler.Geodesics.primeImages F = primeImages F := by
  ext s
  constructor
  · rintro ⟨γ, hγ, hs⟩
    exact ⟨toOrdinary γ, hγ, hs⟩
  · rintro ⟨γ, hγ, hs⟩
    exact ⟨toVariational γ, hγ, hs⟩

theorem infinite_primeImages_iff (F : ReversibleMetric n) :
    (Finsler.Geodesics.primeImages F).Infinite ↔ (primeImages F).Infinite := by
  rw [variational_primeImages_eq]

theorem exists_prime_representative {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    ∃ δ : ClosedGeodesic F, Prime δ ∧ image δ.loop = image γ.loop := by
  obtain ⟨δ, _, _, hδ, _, hi⟩ := Finsler.Geodesics.exists_prime_representative (toVariational γ)
  exact ⟨toOrdinary δ, hδ, hi⟩

/-- Ordinary-coordinate version of the same unproved infinitude assertion. -/
def ReversibleSphereAssertion : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ F : ReversibleMetric n, (primeImages F).Infinite

/-- Statement comparison only; neither side is asserted to hold. -/
theorem assertion_iff :
    Finsler.Geodesics.ReversibleSphereAssertion ↔ ReversibleSphereAssertion := by
  constructor
  · intro h n hn F
    exact (infinite_primeImages_iff F).mp (h n hn F)
  · intro h n hn F
    exact (infinite_primeImages_iff F).mpr (h n hn F)

end

end Finsler.OrdinaryGeodesics
