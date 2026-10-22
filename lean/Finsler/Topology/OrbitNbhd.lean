module

public import Finsler.Topology.PieceAdditive
public import Finsler.Topology.CrossingWK
public import Finsler.Topology.CriticalCircles

/-! Neighbourhoods of the orbits of critical circles. The orbit of a prime closed geodesic image s
at a level c consists of its positive and negative critical circles; it is invariant under the
reversal (which exchanges the two circles) and the half rotation (which preserves each), and it is
compact. The orbits of distinct prime images are disjoint, so with finitely many prime images
there is δ > 0 separating any two of them in the uniform distance. The loops within δ/2 of the
orbit of s form an open set W_s, invariant under the reversal and the half rotation (both do not
increase the uniform distance), containing the orbit; the W_s are pairwise disjoint, and the
loops uniformly within δ/4 of a tangent critical loop of energy c², c > 0, lie in their union.
These are the pieces of the splitting of a single crossing into orbits; with `PieceAdditive`
restriction to the parts of a pair of invariant sets in the W_s is jointly bijective. -/

@[expose] public section

namespace Finsler.OrbitNbhd

open Set Topology Filter
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelLoop Finsler.BorelK Finsler.BorelCoverK
open Finsler.OrientedCritical Finsler.CriticalCircles Finsler.CrossingWK
open Finsler.SobolevCircleRepresentative

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n) (c : ℝ)

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

/-- The orbit of the critical circles of a prime image at a level. -/
def orbitCrit (s : Set (Sphere n)) : Set (SphereLoop n) := posCircle F c s ∪ negCircle F c s

theorem vadd_mem_posCircle (φ : Circ) {s : Set (Sphere n)} {γ : SphereLoop n}
    (hγ : γ ∈ posCircle F c s) : φ +ᵥ γ ∈ posCircle F c s := by
  obtain ⟨hs, k, θ, hk, hck, rfl⟩ := hγ
  exact ⟨hs, k, φ + θ, hk, hck, vadd_vadd φ θ _⟩

theorem half_mem_orbitCrit {s : Set (Sphere n)} {γ : SphereLoop n} (hγ : γ ∈ orbitCrit F c s) :
    half +ᵥ γ ∈ orbitCrit F c s := by
  rcases hγ with h | ⟨γ', hγ', rfl⟩
  · exact Or.inl (vadd_mem_posCircle F c half h)
  · exact Or.inr ⟨half +ᵥ γ', vadd_mem_posCircle F c half hγ', reverse_half γ'⟩

theorem reverse_mem_orbitCrit {s : Set (Sphere n)} {γ : SphereLoop n}
    (hγ : γ ∈ orbitCrit F c s) : reverseSphere γ ∈ orbitCrit F c s := by
  rcases hγ with h | ⟨γ', hγ', rfl⟩
  · exact Or.inr ⟨γ, h, rfl⟩
  · rw [reverseSphere_involutive]
    exact Or.inl hγ'

theorem isCompact_orbitCrit (s : Set (Sphere n)) : IsCompact (orbitCrit F c s) :=
  (isCompact_posCircle F c s).union (isCompact_negCircle F c s)

theorem orbitCrit_disjoint {s s' : Set (Sphere n)} (hne : s ≠ s') :
    Disjoint (orbitCrit F c s) (orbitCrit F c s') := by
  refine Disjoint.union_left (Disjoint.union_right (posCircle_disjoint F c hne)
    (posCircle_negCircle_disjoint F c s s')) (Disjoint.union_right ?_ (negCircle_disjoint F c hne))
  exact (posCircle_negCircle_disjoint F c s' s).symm

/-- The circle maps of the orbits of distinct prime images are separated. -/
theorem exists_orbit_separation (hfin : (primeImages F).Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ primeImages F, ∀ s' ∈ primeImages F, s ≠ s' →
      ∀ γ ∈ orbitCrit F c s, ∀ γ' ∈ orbitCrit F c s',
        δ ≤ dist (sphereCircleMap γ) (sphereCircleMap γ') := by
  have hpair : ∀ p ∈ (primeImages F ×ˢ primeImages F), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      p.1 ≠ p.2 → ∀ γ ∈ orbitCrit F c p.1, ∀ γ' ∈ orbitCrit F c p.2,
        δ ≤ dist (sphereCircleMap γ) (sphereCircleMap γ') := by
    rintro ⟨s, s'⟩ -
    by_cases hne : s = s'
    · exact Eventually.of_forall fun δ h => absurd hne h
    · have hK : IsCompact (sphereCircleMap '' orbitCrit F c s) :=
        (isCompact_orbitCrit F c s).image (sphereCircleMap_continuous n)
      have hK' : IsCompact (sphereCircleMap '' orbitCrit F c s') :=
        (isCompact_orbitCrit F c s').image (sphereCircleMap_continuous n)
      have hdis : Disjoint (sphereCircleMap '' orbitCrit F c s)
          (sphereCircleMap '' orbitCrit F c s') := by
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨γ, hγ, rfl⟩ ⟨γ', hγ', he⟩
        have := sphereCircleMap_injective n he
        subst this
        exact Set.disjoint_left.mp (orbitCrit_disjoint F c hne) hγ hγ'
      obtain ⟨δ₀, hδ₀, hth⟩ := hdis.exists_thickenings hK hK'.isClosed
      filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ _ γ hγ γ' hγ'
      by_contra hlt
      push Not at hlt
      have h1 : sphereCircleMap γ' ∈ Metric.thickening δ₀ (sphereCircleMap '' orbitCrit F c s) :=
        Metric.mem_thickening_iff.mpr ⟨sphereCircleMap γ, ⟨γ, hγ, rfl⟩, by
          rw [dist_comm]
          exact hlt.trans hδ.2⟩
      have h2 : sphereCircleMap γ' ∈ Metric.thickening δ₀ (sphereCircleMap '' orbitCrit F c s') :=
        Metric.self_subset_thickening hδ₀ _ ⟨γ', hγ', rfl⟩
      exact Set.disjoint_left.mp hth h1 h2
  have hall := (eventually_all_finite (hfin.prod hfin)).mpr hpair
  obtain ⟨δ, hδ, hδpos⟩ := (hall.and self_mem_nhdsWithin).exists
  exact ⟨δ, hδpos, fun s hs s' hs' hne γ hγ γ' hγ' => hδ (s, s') ⟨hs, hs'⟩ hne γ hγ γ' hγ'⟩

/-- The loops within r of the orbit of a prime image. -/
def nbhd (r : ℝ) (s : Set (Sphere n)) : Set (Loops n) :=
  {x : Loops n | ∃ γ ∈ orbitCrit F c s,
    dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ) < r}

theorem nbhd_isOpen (r : ℝ) (s : Set (Sphere n)) : IsOpen (nbhd F c r s) :=
  isOpen_near (orbitCrit F c s) r

theorem kInv_nbhd (r : ℝ) (s : Set (Sphere n)) : KInv (nbhd F c r s) where
  rev_mem := by
    rintro u ⟨γ, hγ, hd⟩
    exact ⟨reverseSphere γ, reverse_mem_orbitCrit F c hγ,
      lt_of_le_of_lt (dist_sphereCircleMap_reverse_le u γ) hd⟩
  half_mem := by
    rintro u ⟨γ, hγ, hd⟩
    exact ⟨half +ᵥ γ, half_mem_orbitCrit F c hγ,
      lt_of_le_of_lt (dist_sphereCircleMap_vadd_le half u γ) hd⟩

/-- **Orbit neighbourhoods.** With finitely many prime closed geodesic images, for a level c > 0
there are r > 0 and open sets W_s, one for each prime image, invariant under the reversal and the
half rotation, pairwise disjoint, containing the orbits of critical circles, such that the loops
uniformly within r/2 of a tangent critical loop of energy c² lie in their union. -/
theorem exists_orbit_nhds (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ (∀ s, IsOpen (nbhd F c r s)) ∧ (∀ s, KInv (nbhd F c r s)) ∧
      (Pairwise fun s s' => Disjoint (nbhd F c r s) (nbhd F c r s')) ∧
      (∀ s, ∀ γ ∈ orbitCrit F c s, (γ : Loops n) ∈ nbhd F c r s) ∧
      tube F c (r / 2) ⊆ ⋃ s, nbhd F c r s := by
  obtain ⟨δ, hδ, hsep⟩ := exists_orbit_separation F c hfin
  refine ⟨δ / 2, by positivity, nbhd_isOpen F c _, kInv_nbhd F c _, ?_, ?_, ?_⟩
  · intro s s' hne
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨γ, hγ, hd⟩ ⟨γ', hγ', hd'⟩
    have hs : s ∈ primeImages F := by
      rcases hγ with ⟨hs, -⟩ | ⟨_, ⟨hs, -⟩, -⟩ <;> exact hs
    have hs' : s' ∈ primeImages F := by
      rcases hγ' with ⟨hs', -⟩ | ⟨_, ⟨hs', -⟩, -⟩ <;> exact hs'
    have h := hsep s hs s' hs' hne γ hγ γ' hγ'
    have htri := dist_triangle (sphereCircleMap γ) (sphereCircleMap (x : SphereLoop n))
      (sphereCircleMap γ')
    rw [dist_comm] at hd
    linarith
  · intro s γ hγ
    exact ⟨γ, hγ, by rw [dist_self]; positivity⟩
  · rintro x ⟨γ, hγ, hE, hclose⟩
    have hd : dist (sphereCircleMap (x : SphereLoop n)) (sphereCircleMap γ) < δ / 2 :=
      lt_of_le_of_lt (dist_sphereCircleMap_le (by positivity) _ _ hclose) (by linarith)
    rcases mem_posCrit_or_negCrit F hc γ hγ hE with h | h
    · rw [posCrit_eq] at h
      obtain ⟨s, -, hs⟩ := mem_iUnion₂.mp h
      exact mem_iUnion.mpr ⟨s, γ, Or.inl hs, hd⟩
    · rw [negCrit_eq] at h
      obtain ⟨s, -, hs⟩ := mem_iUnion₂.mp h
      exact mem_iUnion.mpr ⟨s, γ, Or.inr hs, hd⟩

end

end Finsler.OrbitNbhd
