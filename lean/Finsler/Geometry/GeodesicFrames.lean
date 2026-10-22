module

public import Finsler.Geometry.GeodesicIteration
public import Finsler.Geometry.NormalFamily

/-! Closed definite frames along the critical circle of an iterate of a closed geodesic. The
iteration data of a closed geodesic (index function, nullity function, mean index, period) are
fixed once and for all by a choice. For s, m ≥ 1 with gcd(s m, L) = gcd(s, L) and s even or m
odd, and N large, the root polygons are the s-fold iterates of the polygons of 2 N samples of
the closed geodesic at the phases θ; their m-fold iterates are the critical polygons of the
(s m)-fold iterate of the closed geodesic with m s (2 N) vertices. The family of the root
polygons is continuous, the phase θ + 1/(2 N) rotates the vertices by one, the phase θ + 1
gives the same polygon, the m-fold iterates have the nullities of the root polygons and their
indices exceed those of the root polygons by I(s m) - I(s). Hence the normal bundle of the
iterated polygons along the critical circle has continuous closed negative frames of
I(s m) - I(s) vectors and closed positive frames of the complementary number of vectors. -/

@[expose] public section

namespace Finsler.GeodesicFrames

open Module QuadraticForm QuadraticMap Filter Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.PolygonSampling
open Finsler.AmbientSymmetry Finsler.SymmetricBlocks Finsler.AmbientNormalIndex
open Finsler.AmbientRotation Finsler.PolygonIterateReduction Finsler.PhaseNullity
open Finsler.SmoothSobolev Finsler.DefiniteFrames Finsler.NormalFamily
open Finsler.GeodesicIteration
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {F : ReversibleMetric n}

/-- The data of the polygon of 2 N samples of a closed geodesic at the phase a: it is δ-short,
without zero edges and stationary, and its iterates and double iterates have the nullities and
indices given by the functions ν, I and the period L. -/
def SampleData (g : Finsler.Geodesics.ClosedGeodesic F) (I ν : ℕ → ℕ) (L : ℕ) (δ : ℝ) (N : ℕ)
    [NeZero N] (a : ℝ) : Prop :=
  ShortPolygon δ (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))) ∧
  (∀ i, samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)) (i + 1) ≠
    samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)) i) ∧
  PolyCritical F (2 * N) (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))) ∧
  (∀ (m : ℕ) [NeZero m],
    nullity F (iterate m (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) =
        ν (Nat.gcd m L) ∧
    ∀ hs : (hessian F (iterate m (2 * N) (samplePoly (2 * N)
        (ofSmooth (Finsler.Loops.shift g.loop a))))).toLinearMap.IsSymmetric,
      index F (iterate m (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) hs = I m) ∧
  ∀ (d k : ℕ) [NeZero d] [NeZero k],
    nullity F (iterate k (d * (2 * N)) (iterate d (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))))) =
        ν (Nat.gcd (d * k) L) ∧
    ∀ hs : (hessian F (iterate k (d * (2 * N)) (iterate d (2 * N) (samplePoly (2 * N)
        (ofSmooth (Finsler.Loops.shift g.loop a)))))).toLinearMap.IsSymmetric,
      index F (iterate k (d * (2 * N)) (iterate d (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))))) hs = I (d * k)

/-- The iteration data of a closed geodesic. -/
structure IterData (g : Finsler.Geodesics.ClosedGeodesic F) where
  /-- the index function -/
  I : ℕ → ℕ
  /-- the nullity function on the divisors of the period -/
  ν : ℕ → ℕ
  /-- the mean index -/
  Δ : ℝ
  /-- the period -/
  L : ℕ
  mean_nonneg : 0 ≤ Δ
  one_le : 1 ≤ L
  add : ∀ m k, 1 ≤ m → 1 ≤ k → I (m + k) ≤ I m + I k + n ∧ I m + I k ≤ I (m + k) + n
  mean : ∀ m, 1 ≤ m → |(I m : ℝ) - m * Δ| ≤ n
  null_le : ∀ m, 1 ≤ m → ν (Nat.gcd m L) ≤ 2 * n
  data : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (a : ℝ),
    SampleData g I ν L δ N a

/-- A closed geodesic has iteration data. -/
theorem nonempty_iterData (g : Finsler.Geodesics.ClosedGeodesic F) : Nonempty (IterData g) := by
  obtain ⟨I, ν, Δ, L, hΔ, hL, hadd, hmean, hnull, hdata⟩ := exists_iteration_data g
  exact ⟨⟨I, ν, Δ, L, hΔ, hL, hadd, hmean, hnull, hdata⟩⟩

/-- The chosen iteration data of a closed geodesic. -/
def iterData (g : Finsler.Geodesics.ClosedGeodesic F) : IterData g :=
  Classical.choice (nonempty_iterData g)

/-- The root polygons: the s-fold iterates of the polygons of 2 N samples at the phases. -/
def rootFamily (g : Finsler.Geodesics.ClosedGeodesic F) (s N : ℕ) (a : ℝ) :
    ZMod (s * (2 * N)) → Sphere n :=
  iterate s (2 * N) (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))

theorem rootFamily_continuous (g : Finsler.Geodesics.ClosedGeodesic F) (s N : ℕ) [NeZero s]
    [NeZero N] : Continuous fun a : ℝ => amb (rootFamily g s N a) :=
  amb_iterate_sample_continuous g.loop s (2 * N)

/-- The phase a + 1/(2 N) rotates the vertices of the root polygon by one. -/
theorem rootFamily_add (g : Finsler.Geodesics.ClosedGeodesic F) (s N : ℕ) [NeZero s] [NeZero N]
    (a : ℝ) : rootFamily g s N (a + 1 / ((2 * N : ℕ) : ℝ)) = rotP 1 (rootFamily g s N a) := by
  unfold rootFamily
  rw [samplePoly_shift_add]
  have h := iterate_rotP s 1 (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))
  rw [Nat.cast_one, Nat.cast_one] at h
  exact h

/-- The phase a + 1 gives the same root polygon. -/
theorem rootFamily_add_one (g : Finsler.Geodesics.ClosedGeodesic F) (s N : ℕ) (a : ℝ) :
    rootFamily g s N (a + 1) = rootFamily g s N a := by
  unfold rootFamily
  rw [shift_fract g.loop (a + 1), Int.fract_add_one, ← shift_fract]

/-- **Closed frames along the critical circle.** Let L and I be the period and the index
function of the closed geodesic, and s, m ≥ 1 with gcd(s m, L) = gcd(s, L) and s even or m odd.
For N large the normal bundle of the m-fold iterated polygons along the circle of the root
polygons has a continuous closed family of negative frames of I(s m) - I(s) vectors and a
continuous closed family of positive frames of the complementary number of vectors. -/
theorem exists_closed_frames (g : Finsler.Geodesics.ClosedGeodesic F) (s m : ℕ) [NeZero s]
    [NeZero m] (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hpar : Even s ∨ Odd m) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      (∃ H : ℝ → Fin ((iterData g).I (s * m) - (iterData g).I s) →
          normal (rotL (n := n) m (s * (2 * N))) m, Continuous H ∧ H 1 = H 0 ∧
        ∀ θ ∈ Icc (0 : ℝ) 1, Neg (formB m (s * (2 * N)) F (rootFamily g s N) θ) (H θ)) ∧
      ∃ H : ℝ → Fin (finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
            ((iterData g).I (s * m) - (iterData g).I s)) →
          normal (rotL (n := n) m (s * (2 * N))) m, Continuous H ∧ H 1 = H 0 ∧
        ∀ θ ∈ Icc (0 : ℝ) 1, Neg (-formB m (s * (2 * N)) F (rootFamily g s N) θ) (H θ) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_ambientMinEnergy_contDiffAt F
  obtain ⟨N₀, hN₀⟩ := (iterData g).data δ hδpos
  refine ⟨N₀, fun N hN _ => ?_⟩
  have hfacts : ∀ a : ℝ, SampleData g (iterData g).I (iterData g).ν (iterData g).L δ N a :=
    fun a => hN₀ N hN a
  have hq : ∀ a : ℝ, ShortPolygon δ (rootFamily g s N a) := fun a =>
    shortPolygon_iterate s (2 * N) (hfacts a).1
  have hne : ∀ (a : ℝ) i, rootFamily g s N a (i + 1) ≠ rootFamily g s N a i := fun a =>
    iterate_ne s (2 * N) (hfacts a).2.1
  have hc : ∀ a : ℝ, PolyCritical F (s * (2 * N)) (rootFamily g s N a) := fun a =>
    polyCritical_iterate s F hδ (hfacts a).1 (hfacts a).2.1 (hfacts a).2.2.1
  have hNpos : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_neZero (2 * N)
  have hη : (0 : ℝ) < 1 / ((2 * N : ℕ) : ℝ) := div_pos one_pos hNpos
  have hone : ((2 * N : ℕ) : ℝ) * (1 / ((2 * N : ℕ) : ℝ)) = 1 := mul_one_div_cancel hNpos.ne'
  have hper : ∀ a : ℝ, rootFamily g s N (a + ((2 * N : ℕ) : ℝ) * (1 / ((2 * N : ℕ) : ℝ))) =
      rootFamily g s N a := fun a => by
    rw [hone]
    exact rootFamily_add_one g s N a
  have hnull : ∀ a : ℝ, nullity F (iterate m (s * (2 * N)) (rootFamily g s N a)) =
      nullity F (rootFamily g s N a) := fun a => by
    have h1 := ((hfacts a).2.2.2.2 s m).1
    have h2 := ((hfacts a).2.2.2.1 s).1
    unfold rootFamily
    rw [h1, h2, hgcd]
  have hidx0 : ∀ (a : ℝ)
      (hs : (hessian F (iterate m (s * (2 * N)) (rootFamily g s N a))).toLinearMap.IsSymmetric)
      (hs₀ : (hessian F (rootFamily g s N a)).toLinearMap.IsSymmetric),
      index F (iterate m (s * (2 * N)) (rootFamily g s N a)) hs = (iterData g).I (s * m) ∧
        index F (rootFamily g s N a) hs₀ = (iterData g).I s := fun a hs hs₀ =>
    ⟨((hfacts a).2.2.2.2 s m).2 hs, ((hfacts a).2.2.2.1 s).2 hs₀⟩
  have hle : (iterData g).I s ≤ (iterData g).I (s * m) := by
    have hs := hessian_isSymmetric F hδ (shortPolygon_iterate m (s * (2 * N)) (hq 0))
      (iterate_ne m (s * (2 * N)) (hne 0))
    have hs₀ := hessian_isSymmetric F hδ (hq 0) (hne 0)
    have h := index_iterate_eq_add m (s * (2 * N)) F hδ
      (shortPolygon_iterate m (s * (2 * N)) (hq 0)) (iterate_ne m (s * (2 * N)) (hne 0)) (hq 0)
      (hne 0) (polyCritical_iterate m F hδ (hq 0) (hne 0) (hc 0)) (hc 0) zero_le_one hs hs₀
    rw [(hidx0 0 hs hs₀).1, (hidx0 0 hs hs₀).2] at h
    omega
  have hidx : ∀ (a : ℝ)
      (hs : (hessian F (iterate m (s * (2 * N)) (rootFamily g s N a))).toLinearMap.IsSymmetric)
      (hs₀ : (hessian F (rootFamily g s N a)).toLinearMap.IsSymmetric),
      index F (iterate m (s * (2 * N)) (rootFamily g s N a)) hs =
        index F (rootFamily g s N a) hs₀ +
          ((iterData g).I (s * m) - (iterData g).I s) := fun a hs hs₀ => by
    rw [(hidx0 a hs hs₀).1, (hidx0 a hs hs₀).2]
    omega
  have h := NormalFamily.exists_closed_frames m (s * (2 * N)) F hδ
    (rootFamily_continuous g s N) hq hne hc (rootFamily_add g s N) (s := s) (r := N)
    (Nat.pos_of_neZero N) hη rfl hpar hper hnull hidx
  rw [hone] at h
  exact h

end

end Finsler.GeodesicFrames
