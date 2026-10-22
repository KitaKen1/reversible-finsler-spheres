module

public import Finsler.Topology.PolygonCrossing
public import Finsler.Topology.OrientedCritical
public import Finsler.Geometry.PolygonModel

/-! The crossing pairs of the polygon energy at a critical level split into a positive and a
negative part. For a polygon model and an open set U of loops, the polygons near U are the
short polygons whose broken geodesic lies in U; they form an open set, and disjoint open sets
of loops give disjoint sets of polygons. A stationary short polygon of positive energy has a
tangent critical broken geodesic of the same energy; so if c is the only critical level in
[a₀, b₀], the stationary polygons of energy in [a₀², b₀²] have broken geodesics which are positive
or negative critical loops of level c. With finitely many prime closed geodesic images these
two sets of loops are compact and disjoint, hence have disjoint open neighbourhoods U₊, U₋, and
the polygons near U₊ and near U₋ are disjoint open sets containing the stationary polygons of
the band. Therefore the crossing pairs of the polygon energy for tight cuts in the band have
the product of the cohomologies of the lens pairs near U₊ and near U₋. -/

@[expose] public section

namespace Finsler.PolygonOriented

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonModel Finsler.PolygonDescent
open Finsler.PolygonCrossing Finsler.CriticalLevels Finsler.OrientedCritical Finsler.FlowLens
open Finsler.LensContinuation Finsler.BorelCochain Finsler.BorelLoop Finsler.PairTriple
open Finsler.SobolevCurveVariation
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {F : ReversibleMetric n} {A : ℝ} {N : ℕ} [NeZero N]
  (M : PolygonModelData F A N)

/-- The short polygons whose broken geodesic lies in a set of loops. -/
def near (U : Set (SphereLoop n)) : Set (Poly n N) :=
  {q | ∃ hq : ShortPolygon M.δ q, broken M ⟨q, hq⟩ ∈ U}

theorem near_isOpen {U : Set (SphereLoop n)} (hU : IsOpen U) : IsOpen (near M U) := by
  have himg : near M U = Subtype.val '' (broken M ⁻¹' U) := by
    ext q
    constructor
    · rintro ⟨hq, hU'⟩
      exact ⟨⟨q, hq⟩, hU', rfl⟩
    · rintro ⟨⟨q', hq'⟩, hU', rfl⟩
      exact ⟨hq', hU'⟩
  rw [himg]
  exact (shortPolygon_isOpen M.δ N).isOpenMap_subtype_val _
    (hU.preimage (broken_continuous M))

theorem near_disjoint {U U' : Set (SphereLoop n)} (h : Disjoint U U') :
    Disjoint (near M U) (near M U') := by
  rw [Set.disjoint_left]
  rintro q ⟨hq, h1⟩ ⟨_, h2⟩
  exact Set.disjoint_left.mp h h1 h2

/-- The broken geodesic of a stationary polygon of the band is a positive or a negative
critical loop of the only critical level of the band. -/
theorem broken_mem_crit {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) (hc : PolyCritical F N q)
    (ha : a₀ ^ 2 ≤ PolygonDescent.energy F N q) (hb : PolygonDescent.energy F N q ≤ b₀ ^ 2) :
    broken M ⟨q, hq⟩ ∈ posCrit F c ∪ negCrit F c := by
  have htc : TangentCritical F (broken M ⟨q, hq⟩) := tangentCritical_of_polyCritical F M.seg hq hc
  have hE : SobolevEnergy.energy F (broken M ⟨q, hq⟩) = PolygonDescent.energy F N q :=
    energy_broken M ⟨q, hq⟩
  have hpos : 0 < SobolevEnergy.energy F (broken M ⟨q, hq⟩) := by
    rw [hE]
    exact lt_of_lt_of_le (by positivity) ha
  have hb₀ : 0 ≤ b₀ := ha₀.le.trans hab₀
  have hlevel : Real.sqrt (SobolevEnergy.energy F (broken M ⟨q, hq⟩)) = c := by
    apply hone _ (crit_mem F _ htc hpos)
    · rw [hE]
      calc a₀ = Real.sqrt (a₀ ^ 2) := (Real.sqrt_sq ha₀.le).symm
        _ ≤ Real.sqrt (PolygonDescent.energy F N q) := Real.sqrt_le_sqrt ha
    · rw [hE]
      calc Real.sqrt (PolygonDescent.energy F N q) ≤ Real.sqrt (b₀ ^ 2) := Real.sqrt_le_sqrt hb
        _ = b₀ := Real.sqrt_sq hb₀
  have hcpos : 0 < c := by
    rw [← hlevel]
    exact Real.sqrt_pos.mpr hpos
  have hEc : SobolevEnergy.energy F (broken M ⟨q, hq⟩) = c ^ 2 := by
    rw [← hlevel, Real.sq_sqrt hpos.le]
  exact mem_posCrit_or_negCrit F hcpos _ htc hEc

/-- With finitely many prime closed geodesic images, the crossing pairs of the polygon energy
for tight cuts around the only critical level of a band are products of the lens pairs in two
disjoint open sets: the polygons near the positive and near the negative critical loops. -/
theorem exists_oriented_decomposition (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < M.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ ^ 2 →
      ShortPolygon M.δ q) :
    ∃ Up Um : Set (SphereLoop n), IsOpen Up ∧ IsOpen Um ∧ Disjoint Up Um ∧
      posCrit F c ⊆ Up ∧ negCrit F c ⊆ Um ∧
      ∃ D : Descent (Poly n N) (PolygonDescent.energy F N), ∃ d : ℝ, 0 < d ∧
        ∀ (a' a b T : ℝ) (hab : a ≤ b) (hT : 0 ≤ T), a₀ ^ 2 ≤ a' → a' < a → b ≤ b₀ ^ 2 →
          b - a' < d → 1 ≤ T → ∀ k : ℕ,
          Nonempty (H (triv (pairOf ((sub_subset_lensY D hab hT).trans
              (lensY_subset D a b T)))) k ≃ₗ[ZMod 2]
            (H (triv (pairOf (partY_sub_partU (PolygonDescent.energy F N) D (near M Up)
                a b T))) k ×
              H (triv (pairOf (partY_sub_partU (PolygonDescent.energy F N) D (near M Um)
                a b T))) k)) := by
  have hdis : Disjoint (posCrit F c) (negCrit F c) :=
    Set.disjoint_left.mpr fun γ hp hm => posCrit_inter_negCrit F c γ hp hm
  obtain ⟨Up, Um, hUp, hUm, hpU, hmU, hUU⟩ :=
    SeparatedNhds.of_isCompact_isCompact (isCompact_posCrit F hfin c)
      (isCompact_negCrit F hfin c) hdis
  refine ⟨Up, Um, hUp, hUm, hUU, hpU, hmU, ?_⟩
  exact exists_crossing_decomposition F hn hC hshort (near_isOpen M hUp) (near_isOpen M hUm)
    (near_disjoint M hUU) (fun q ha hb hc => by
      rcases broken_mem_crit M ha₀ hab₀ hone (hshort q hb) hc ha hb with h | h
      · exact Or.inl ⟨hshort q hb, hpU h⟩
      · exact Or.inr ⟨hshort q hb, hmU h⟩)

end

end Finsler.PolygonOriented
