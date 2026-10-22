module

public import Finsler.Topology.PolygonOriented
public import Finsler.Topology.LensFamily
public import Finsler.Topology.CriticalCircles

/-! The crossing pairs of the polygon energy at a critical level split into the labels of the
critical circles. Let M be a polygon model, c the only critical level in [a₀, b₀], and let the
polygons of energy at most b₀² be short. For every open set U of loops containing the critical
loops of level c there are a descent of the polygon energy and d > 0 such that for cuts
a₀² ≤ a' < b ≤ b₀² with b − a' < d and every time T ≥ 1 the polygons below b which are not taken
below a' in time T are near U. With finitely many prime closed geodesic images and pairwise
disjoint open neighbourhoods U_ℓ of the critical circles of the labels ℓ (a prime image with an
orientation), the cohomology of the polygons below b relative to those below a therefore
vanishes in a degree in which the lens pairs near all U_ℓ have no cohomology, it is finite
dimensional if these are, of dimension the sum of their dimensions, and conversely the lens
pairs have finite dimensional cohomology if the crossing has. Such neighbourhoods exist. -/

@[expose] public section

namespace Finsler.PolygonCircles

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonModel Finsler.PolygonDescent
open Finsler.PolygonCrossing Finsler.CriticalLevels Finsler.OrientedCritical Finsler.FlowLens
open Finsler.LensContinuation Finsler.LensTrap Finsler.BorelCochain Finsler.BorelLoop
open Finsler.PairTriple Finsler.PolygonOriented Finsler.CriticalCircles Finsler.LensFamily
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {F : ReversibleMetric n} {A : ℝ} {N : ℕ} [NeZero N]
  (M : PolygonModelData F A N)

/-- The polygons near a finite union of sets of loops. -/
theorem near_biUnion {ι : Type*} (s : Finset ι) (U : ι → Set (SphereLoop n)) :
    near M (⋃ i ∈ s, U i) = ⋃ i ∈ s, near M (U i) := by
  ext q
  constructor
  · rintro ⟨hq, h⟩
    obtain ⟨i, hi, hU⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨i, hi, hq, hU⟩
  · intro h
    obtain ⟨i, hi, hq, hU⟩ := mem_iUnion₂.mp h
    exact ⟨hq, mem_iUnion₂.mpr ⟨i, hi, hU⟩⟩

/-- A descent of the polygon energy for which the polygons of a band which are not taken below
the lower cut are near a given open set of loops containing the critical loops of the only
critical level of the band. -/
theorem exists_trap_near (hn : 1 ≤ n)
    (hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < M.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ ^ 2 →
      ShortPolygon M.δ q)
    {U : Set (SphereLoop n)} (hU : IsOpen U) (hcrit : posCrit F c ∪ negCrit F c ⊆ U) :
    ∃ D : Descent (Poly n N) (PolygonDescent.energy F N), ∃ d : ℝ, 0 < d ∧
      ∀ a' b T : ℝ, a₀ ^ 2 ≤ a' → b ≤ b₀ ^ 2 → b - a' < d → 1 ≤ T →
        ∀ w : Poly n N, PolygonDescent.energy F N w < b →
          a' ≤ PolygonDescent.energy F N (D.flow T w) → w ∈ near M U := by
  have hcr : ∀ q : ZMod N → Sphere n, a₀ ^ 2 ≤ PolygonDescent.energy F N q →
      PolygonDescent.energy F N q ≤ b₀ ^ 2 → PolyCritical F N q → q ∈ near M U :=
    fun q ha hb hc =>
      ⟨hshort q hb, hcrit (broken_mem_crit M ha₀ hab₀ hone (hshort q hb) hc ha hb)⟩
  obtain ⟨D, hD⟩ := exists_descent F hn hC hshort (near_isOpen M hU) hcr
  obtain ⟨d, hd, htr⟩ := exists_trap D (energy_continuous F hn N) (near_isOpen M hU)
    (band_isCompact F hn N (a₀ ^ 2) (b₀ ^ 2)) (fun w ha hb hw => hD w ha hb hw)
  exact ⟨D, d, hd, fun a' b T ha hb hw hT => htr a' b T ha hb hw hT⟩

/-- With finitely many prime closed geodesic images, the crossing pairs of the polygon energy
for tight cuts around the only critical level of a band split into the lens pairs near pairwise
disjoint open neighbourhoods of the critical circles: vanishing, finiteness and dimensions. -/
theorem exists_label_decomposition (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < M.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ ^ 2 →
      ShortPolygon M.δ q)
    {U : Set (Sphere n) × Bool → Set (SphereLoop n)}
    (hU : ∀ ℓ ∈ labels F hfin, IsOpen (U ℓ) ∧ circle F c ℓ ⊆ U ℓ)
    (hdis : ((labels F hfin : Finset (Set (Sphere n) × Bool)) :
      Set (Set (Sphere n) × Bool)).PairwiseDisjoint U) :
    ∃ D : Descent (Poly n N) (PolygonDescent.energy F N), ∃ d : ℝ, 0 < d ∧
      ∀ (a' a b T : ℝ) (hab : a ≤ b), a₀ ^ 2 ≤ a' → a' < a → b ≤ b₀ ^ 2 → b - a' < d → 1 ≤ T →
        ∀ k : ℕ,
          ((∀ ℓ ∈ labels F hfin, ∀ x : lensH D (near M (U ℓ)) a b T k, x = 0) →
            ∀ x : crossH (PolygonDescent.energy F N) hab k, x = 0) ∧
          ((∀ ℓ ∈ labels F hfin, Module.Finite (ZMod 2) (lensH D (near M (U ℓ)) a b T k)) →
            Module.Finite (ZMod 2) (crossH (PolygonDescent.energy F N) hab k) ∧
              Module.finrank (ZMod 2) (crossH (PolygonDescent.energy F N) hab k) =
                ∑ ℓ ∈ labels F hfin, Module.finrank (ZMod 2)
                  (lensH D (near M (U ℓ)) a b T k)) ∧
          (Module.Finite (ZMod 2) (crossH (PolygonDescent.energy F N) hab k) →
            ∀ ℓ ∈ labels F hfin, Module.Finite (ZMod 2) (lensH D (near M (U ℓ)) a b T k)) := by
  have hopenU : IsOpen (⋃ ℓ ∈ labels F hfin, U ℓ) := isOpen_biUnion fun ℓ hℓ => (hU ℓ hℓ).1
  have hcrit : posCrit F c ∪ negCrit F c ⊆ ⋃ ℓ ∈ labels F hfin, U ℓ := by
    rw [crit_eq F c hfin]
    exact iUnion₂_mono fun ℓ hℓ => (hU ℓ hℓ).2
  obtain ⟨D, d, hd, htr⟩ := exists_trap_near M hn hC ha₀ hab₀ hone hshort hopenU hcrit
  refine ⟨D, d, hd, ?_⟩
  intro a' a b T hab ha0 ha hb0 hwidth hT1 k
  have hT : 0 ≤ T := zero_le_one.trans hT1
  have hg := energy_continuous F hn N
  have hopen : ∀ ℓ ∈ labels F hfin, IsOpen (near M (U ℓ)) :=
    fun ℓ hℓ => near_isOpen M (hU ℓ hℓ).1
  have hdis' : ((labels F hfin : Finset (Set (Sphere n) × Bool)) :
      Set (Set (Sphere n) × Bool)).PairwiseDisjoint fun ℓ => near M (U ℓ) :=
    fun ℓ hℓ ℓ' hℓ' hne => near_disjoint M (hdis hℓ hℓ' hne)
  have htrap : ∀ w : Poly n N, PolygonDescent.energy F N w < b →
      a' ≤ PolygonDescent.energy F N (D.flow T w) → w ∈ ⋃ ℓ ∈ labels F hfin, near M (U ℓ) := by
    intro w hw hw'
    rw [← near_biUnion]
    exact htr a' b T ha0 hb0 hwidth hT1 w hw hw'
  exact ⟨fun hz => LensFamily.crossing_eq_zero D (labels F hfin) hg hab ha hT hopen hdis' htrap k hz,
    fun hf => LensFamily.crossing_finrank D (labels F hfin) hg hab ha hT hopen hdis' htrap k hf,
    fun hf ℓ hℓ => LensFamily.label_finite D (labels F hfin) hg hab ha hT hopen hdis' htrap k hf hℓ⟩

/-- Pairwise disjoint open neighbourhoods of the critical circles with the label decomposition
exist. -/
theorem exists_circle_labels (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < M.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ ^ 2 →
      ShortPolygon M.δ q) :
    ∃ U : Set (Sphere n) × Bool → Set (SphereLoop n),
      (∀ ℓ ∈ labels F hfin, IsOpen (U ℓ) ∧ circle F c ℓ ⊆ U ℓ) ∧
      ((labels F hfin : Finset (Set (Sphere n) × Bool)) :
        Set (Set (Sphere n) × Bool)).PairwiseDisjoint U ∧
      ∃ D : Descent (Poly n N) (PolygonDescent.energy F N), ∃ d : ℝ, 0 < d ∧
        ∀ (a' a b T : ℝ) (hab : a ≤ b), a₀ ^ 2 ≤ a' → a' < a → b ≤ b₀ ^ 2 → b - a' < d →
          1 ≤ T → ∀ k : ℕ,
            (Module.Finite (ZMod 2) (crossH (PolygonDescent.energy F N) hab k) →
              (∀ ℓ ∈ labels F hfin,
                Module.Finite (ZMod 2) (lensH D (near M (U ℓ)) a b T k)) ∧
              Module.finrank (ZMod 2) (crossH (PolygonDescent.energy F N) hab k) =
                ∑ ℓ ∈ labels F hfin, Module.finrank (ZMod 2)
                  (lensH D (near M (U ℓ)) a b T k)) := by
  obtain ⟨U, hU, hdis⟩ := exists_circle_nhds F c hfin
  obtain ⟨D, d, hd, h⟩ := exists_label_decomposition M hn hfin hC ha₀ hab₀ hone hshort hU hdis
  refine ⟨U, hU, hdis, D, d, hd, ?_⟩
  intro a' a b T hab ha0 ha hb0 hwidth hT1 k hfinite
  obtain ⟨-, h2, h3⟩ := h a' a b T hab ha0 ha hb0 hwidth hT1 k
  exact ⟨h3 hfinite, (h2 (h3 hfinite)).2⟩

end

end Finsler.PolygonCircles
