module

public import Finsler.Geometry.PolygonDescentK
public import Finsler.Topology.LensK
public import Finsler.Topology.LensTrap

/-! The K-action on the polygon space and equivariant lens decompositions of polygon crossings.
The reversal of the vertices and the rotation of the vertices by an element of order two are
commuting involutions of the space of sphere polygons. For pairwise disjoint invariant open sets
containing the stationary polygons of a compact energy band, the equivariant descent
(`PolygonDescentK`) decreases the energy strictly in time one at the polygons of the band outside
their union, so for tight cuts the polygons below b which the flow does not take below a' in time
T ≥ 1 lie in the union (`LensTrap`). Then `LensK` decomposes the K-Borel cohomology of the polygon
crossing pair into the lens pairs of the open sets. -/

@[expose] public section

namespace Finsler.PolygonLensK

open Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.PolygonDescent Finsler.PolygonDescentK Finsler.FlowLens Finsler.InvPairs
open Finsler.EnergyDiagonal Finsler.EnergySphereSmooth

noncomputable section

variable {n : ℕ}

theorem reversePolygon_rotPoly {N : ℕ} {s : ZMod N} (hs : s + s = 0) (q : ZMod N → Sphere n) :
    reversePolygon (rotPoly s q) = rotPoly s (reversePolygon q) := by
  funext i
  change q (-i + s) = q (-(i + s))
  have : s = -s := eq_neg_of_add_eq_zero_left hs
  rw [neg_add, ← this]

/-- The reversal and the rotation by an element of order two of the vertices of polygons. -/
def polyK (n N : ℕ) {s : ZMod N} (hs : s + s = 0) : KAct (Poly n N) where
  ρ := ⟨reversePolygon, continuous_pi fun i => continuous_apply (-i)⟩
  σ := ⟨rotPoly s, continuous_pi fun i => continuous_apply (i + s)⟩
  ρρ := reversePolygon_reversePolygon
  σσ := rotPoly_rotPoly hs
  ρσ := reversePolygon_rotPoly hs

/-- **Equivariant descents with trapping.** For pairwise disjoint open sets of polygons invariant
under the reversal and the rotation by s, containing the stationary polygons of the energy band
[a₀, b₀], there is a descent commuting with both such that for tight cuts the polygons below b
which the flow does not take below a' in time T ≥ 1 lie in one of the open sets. -/
theorem exists_descent_trap (F : ReversibleMetric n) (hn : 1 ≤ n) {N : ℕ} [NeZero N]
    {s : ZMod N} (hs : s + s = 0) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ} (hshort : ∀ q : ZMod N → Sphere n, energy F N q ≤ b₀ → ShortPolygon δ q)
    {J : Type} (𝒲 : J → Set (Poly n N)) (h𝒲 : ∀ j, IsOpen (𝒲 j))
    (h𝒲K : ∀ j, Inv (polyK n N hs) (𝒲 j))
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ energy F N q → energy F N q ≤ b₀ →
      PolyCritical F N q → ∃ j, q ∈ 𝒲 j) :
    ∃ D : Descent (Poly n N) (energy F N),
      (∀ t w, D.flow t ((polyK n N hs).ρ w) = (polyK n N hs).ρ (D.flow t w)) ∧
      (∀ t w, D.flow t ((polyK n N hs).σ w) = (polyK n N hs).σ (D.flow t w)) ∧
      ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, a₀ ≤ a → b ≤ b₀ → b - a < d → 1 ≤ T →
        ∀ w, energy F N w < b → a ≤ energy F N (D.flow T w) → ∃ j, w ∈ 𝒲 j := by
  have hU : IsOpen (⋃ j, 𝒲 j) := isOpen_iUnion h𝒲
  obtain ⟨D, hDr, hDh, hstrict⟩ := exists_descent_K F hn hs hδ hshort hU
    (fun q hq => by
      obtain ⟨j, hj⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨j, (h𝒲K j).ρ_mem q hj⟩)
    (fun q hq => by
      obtain ⟨j, hj⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨j, (h𝒲K j).σ_mem q hj⟩)
    (fun q h1 h2 hc => by
      obtain ⟨j, hj⟩ := hcrit q h1 h2 hc
      exact mem_iUnion.mpr ⟨j, hj⟩)
  have hK : IsCompact {w : Poly n N | a₀ ≤ energy F N w ∧ energy F N w ≤ b₀} :=
    ((isClosed_le continuous_const (energy_continuous F hn N)).inter
      (isClosed_le (energy_continuous F hn N) continuous_const)).isCompact
  obtain ⟨d, hd, htrap⟩ := Finsler.LensTrap.exists_trap D (energy_continuous F hn N) hU hK
    hstrict
  refine ⟨D, hDr, hDh, d, hd, fun a b T ha hb hab hT w hw hw' => ?_⟩
  exact mem_iUnion.mp (htrap a b T ha hb hab hT w hw hw')

end

end Finsler.PolygonLensK
