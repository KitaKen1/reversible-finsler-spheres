module

public import Finsler.Topology.PairedCirclePacket
public import Finsler.Analysis.ReversalSeparation
public import Finsler.Geometry.CircleSampling

/-! geometric coverage and separated ambient neighbourhoods for
the actual-circle packet construction. -/

@[expose] public section

namespace Finsler.CirclePacketGeometry

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.PolygonModel Finsler.PolygonDescent Finsler.PolygonSampling Finsler.PolygonCritical
open Finsler.PolygonLoop
open Finsler.RootIsolation Finsler.PairedCirclePacket Finsler.ReversalSeparation
open Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.PolygonDescentK
open Finsler.IntervalSobolev Finsler.CircleRoot Finsler.CircleSampling Finsler.SamplePhase
open Finsler.SmoothSobolev
noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5

variable {n K : ℕ} [NeZero K] {F : ReversibleMetric n} {A : ℝ}

def active (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (c : ℝ) :
    Finset (Set (Sphere n)) := by
  classical
  exact hfin.toFinset.filter fun s => (posCircle F c s).Nonempty

abbrev Active (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (c : ℝ) :=
  {s // s ∈ active F hfin c}

theorem active_mem_prime (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (c : ℝ) (i : Active F hfin c) : i.1 ∈ primeImages F := by
  classical
  exact hfin.mem_toFinset.mp (Finset.mem_filter.mp i.2).1

theorem active_covers (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (c : ℝ)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (hcirc : (circle F c ℓ).Nonempty) :
    ∃ i : Active F hfin c, i.1 = ℓ.1 := by
  classical
  rcases ℓ with ⟨s, o⟩
  have hs := (mem_labels F hfin (s, o)).mp hℓ
  have hp : (posCircle F c s).Nonempty := by
    cases o
    · obtain ⟨_, u, hu, -⟩ := hcirc
      exact ⟨u, hu⟩
    · exact hcirc
  exact ⟨⟨s, Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hs, hp⟩⟩, rfl⟩

theorem exists_multiplicity (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (c : ℝ) (i : Active F hfin c) :
    ∃ k : ℕ, 0 < k ∧ ∀ hs : i.1 ∈ primeImages F,
      (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F i.1 hs).loop) = c := by
  classical
  obtain ⟨u, _, k, _, hk, hkc, -⟩ := (Finset.mem_filter.mp i.2).2
  exact ⟨k, hk, fun _ => hkc⟩

theorem critical_band_cover (M : PolygonModelData F A K) (hfin : (primeImages F).Finite)
    {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    (hshort : ∀ q : ZMod K → Sphere n, PolygonDescent.energy F K q ≤ b₀ ^ 2 → ShortPolygon M.δ q)
    {q : ZMod K → Sphere n} (hq : PolyCritical F K q)
    (ha : a₀ ^ 2 ≤ PolygonDescent.energy F K q) (hb : PolygonDescent.energy F K q ≤ b₀ ^ 2) :
    ∃ p : Active F hfin c × Bool, (incl q : Om n K).1 ∈
      sampleSet K (circle F c (p.1.1, p.2)) := by
  obtain ⟨ℓ, hℓ, hmem, hsamp⟩ := crit_mem_sampleSet M hfin ha₀ hab₀ hone hshort hq ha hb
  obtain ⟨i, hi⟩ := active_covers F hfin c ℓ hℓ ⟨_, hmem⟩
  refine ⟨(i, ℓ.2), ?_⟩
  have he : (i.1, ℓ.2) = ℓ := Prod.ext hi rfl
  rw [he]
  exact hsamp

theorem sampleSet_disjoint (M : PolygonModelData F A K) {S T : Set (SphereLoop n)}
    (hS : ∀ u ∈ S, ∃ hq : ShortPolygon M.δ (samplePoly K u), broken M ⟨samplePoly K u, hq⟩ = u)
    (hT : ∀ u ∈ T, ∃ hq : ShortPolygon M.δ (samplePoly K u), broken M ⟨samplePoly K u, hq⟩ = u)
    (hdis : Disjoint S T) : Disjoint (sampleSet K S) (sampleSet K T) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  obtain ⟨hqu, hbu⟩ := hS u hu
  obtain ⟨hqv, hbv⟩ := hT v hv
  have hq : samplePoly K v = samplePoly K u := by
    funext j
    apply Subtype.ext
    exact congrFun he j
  have hqp : (⟨samplePoly K v, hqv⟩ : {q : ZMod K → Sphere n // ShortPolygon M.δ q}) =
      ⟨samplePoly K u, hqu⟩ := Subtype.ext hq
  have huv := congrArg (broken M) hqp
  rw [hbv, hbu] at huv
  exact Set.disjoint_left.mp hdis hu (huv ▸ hv)

theorem exists_circle_neighbourhoods {ι : Type*} [Fintype ι]
    (M : PolygonModelData F A K) (c : ℝ) (s : ι → Set (Sphere n)) (hinj : Function.Injective s)
    (hrec : ∀ p : ι × Bool, ∀ u ∈ circle F c (s p.1, p.2),
      ∃ hq : ShortPolygon M.δ (samplePoly K u), broken M ⟨samplePoly K u, hq⟩ = u) :
    ∃ U : ι → Set (ZMod K → Ambient n),
      (∀ i, IsOpen (U i) ∧ ∀ u ∈ posCircle F c (s i), amb (samplePoly K u) ∈ U i) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      ∀ i j, Disjoint (U i) (revA K ⁻¹' U j) := by
  have hcmp : ∀ i, IsCompact (sampleSet K (posCircle F c (s i))) :=
    fun i => sampleSet_isCompact (isCompact_circle F c (s i, true))
  have hd : ∀ i j, i ≠ j → Disjoint (sampleSet K (posCircle F c (s i)))
      (sampleSet K (posCircle F c (s j))) := fun i j hij =>
    sampleSet_disjoint M (hrec (i, true)) (hrec (j, true))
      (posCircle_disjoint F c (fun he => hij (hinj he)))
  have hcross : ∀ i j, Disjoint (sampleSet K (posCircle F c (s i)))
      (revA K ⁻¹' sampleSet K (posCircle F c (s j))) := by
    intro i j
    rw [← sampleSet_neg F c (s j)]
    exact sampleSet_disjoint M (hrec (i, true)) (hrec (j, false))
      (posCircle_negCircle_disjoint F c (s i) (s j))
  obtain ⟨U, hU, hdis, hrev⟩ := exists_separated_neighbourhoods (revA K) (revA_revA K)
    (fun i => sampleSet K (posCircle F c (s i))) hcmp hd hcross
  exact ⟨U, fun i => ⟨(hU i).1, fun u hu => (hU i).2 ⟨u, hu, rfl⟩⟩, hdis, hrev⟩

theorem circle_reconstruction (M : PolygonModelData F A K) {c : ℝ} (hc : 0 < c)
    (s : Set (Sphere n)) (hs : s ∈ primeImages F) (o : Bool) (k N : ℕ) [NeZero N]
    (hN : 1 < 2 * N) (hK : k * (2 * N) = K)
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c)
    (hf : ∀ a : ℝ, SampleFacts M.toSegmentData
      (ofSmooth (Finsler.Loops.shift (labelGeod F (s, o) hs).loop a)) (2 * N)) :
    ∀ u ∈ circle F c (s, o), ∃ hq : ShortPolygon M.δ (samplePoly K u),
      broken M ⟨samplePoly K u, hq⟩ = u := by
  rw [circle_eq F hc (s, o) hs hkc]
  rintro _ ⟨a, rfl⟩
  have hq := short_iterate M.toSegmentData (labelGeod F (s, o) hs).loop k hN hf hK a
  exact ⟨hq, broken_iterate M.toSegmentData (labelGeod F (s, o) hs).loop k hN hf hK a hq⟩

end

end Finsler.CirclePacketGeometry
