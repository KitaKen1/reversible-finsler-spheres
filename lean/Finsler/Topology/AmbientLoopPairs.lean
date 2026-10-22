module

public import Finsler.Geometry.AmbientDescent
public import Finsler.Topology.PolygonLoopPairs
public import Finsler.Topology.PolygonCircles

/-! The crossing pairs of the loop space in the ambient polygon space. For a polygon model, the
ordinary cohomology of the loop pair (t_b, t_a) is that of the sublevel pair of the penalized
polygon energy for the cuts a², b² on the ambient polygons with nonzero vertices: sampling
compares the loop pair with the polygon pair, and normalization compares the polygon pair with
the ambient pair. The ambient polygons whose normalization is near an open set of loops form an
open set. With finitely many prime closed geodesic images and pairwise disjoint open
neighbourhoods of the critical circles of the only critical level of a band, there are a
descent of the penalized energy and d > 0 such that the ambient crossing pairs for tight cuts
split into the lens pairs near the critical circles: vanishing, finiteness and dimensions. -/

@[expose] public section

namespace Finsler.AmbientLoopPairs

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonModel Finsler.PolygonDescent
open Finsler.PolygonCrossing Finsler.CriticalLevels Finsler.OrientedCritical Finsler.FlowLens
open Finsler.LensContinuation Finsler.BorelCochain Finsler.BorelLoop Finsler.PairTriple
open Finsler.PolygonOriented Finsler.CriticalCircles Finsler.LensFamily
open Finsler.PolygonLoopPairs Finsler.AmbientPenalty Finsler.AmbientDescent
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {F : ReversibleMetric n} {A : ℝ} {N : ℕ} [NeZero N]
  (M : PolygonModelData F A N)

/-- The loop pair (t_b, t_a) has the cohomology of the sublevel pair of the penalized energy
for the cuts a², b². -/
theorem nonempty_loop_equiv {lam : ℝ} (hlam : 0 ≤ lam) {a b : ℝ}
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q < b ^ 2 →
      ShortPolygon M.δ q)
    (ha : 0 < a) (hab : a ≤ b) (hbA : b ≤ A) (k : ℕ) :
    Nonempty (H (triv (pairOf (lev_mono F hab))) k ≃ₗ[ZMod 2]
      crossH (penW F N lam) (pow_le_pow_left₀ ha.le hab 2) k) := by
  let e₁ := LinearEquiv.ofBijective _ (sample_bijective M hshort ha hab hbA k)
  let e₂ := LinearEquiv.ofBijective _
    (normalize_bijective F (N := N) hlam (pow_le_pow_left₀ ha.le hab 2) k)
  exact ⟨e₁.symm.trans e₂⟩

/-- The ambient polygons whose normalization is near a set of loops. -/
def nearOm (U : Set (SphereLoop n)) : Set (Om n N) := normalizeP ⁻¹' near M U

theorem nearOm_isOpen {U : Set (SphereLoop n)} (hU : IsOpen U) : IsOpen (nearOm M U) :=
  (near_isOpen M hU).preimage normalizeP.continuous

theorem nearOm_disjoint {U U' : Set (SphereLoop n)} (h : Disjoint U U') :
    Disjoint (nearOm M U) (nearOm M U') :=
  (near_disjoint M h).preimage _

theorem incl_mem_nearOm {U : Set (SphereLoop n)} {q : Poly n N} (hq : q ∈ near M U) :
    incl q ∈ nearOm M U := by
  change normalizeP (incl q) ∈ near M U
  rw [normalizeP_incl]
  exact hq

/-- With finitely many prime closed geodesic images, the crossing pairs of the penalized energy
for tight cuts around the only critical level of a band split into the lens pairs near pairwise
disjoint open neighbourhoods of the critical circles. -/
theorem exists_ambient_labels (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {lam : ℝ}
    (hlam : 0 < lam)
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
    ∃ D : Descent (Om n N) (penW F N lam), ∃ d : ℝ, 0 < d ∧
      ∀ (a' a b T : ℝ) (hab : a ≤ b), a₀ ^ 2 ≤ a' → a' < a → b ≤ b₀ ^ 2 → b - a' < d → 1 ≤ T →
        ∀ k : ℕ,
          ((∀ ℓ ∈ labels F hfin, ∀ x : lensH D (nearOm M (U ℓ)) a b T k, x = 0) →
            ∀ x : crossH (penW F N lam) hab k, x = 0) ∧
          ((∀ ℓ ∈ labels F hfin, Module.Finite (ZMod 2) (lensH D (nearOm M (U ℓ)) a b T k)) →
            Module.Finite (ZMod 2) (crossH (penW F N lam) hab k) ∧
              Module.finrank (ZMod 2) (crossH (penW F N lam) hab k) =
                ∑ ℓ ∈ labels F hfin, Module.finrank (ZMod 2)
                  (lensH D (nearOm M (U ℓ)) a b T k)) ∧
          (Module.Finite (ZMod 2) (crossH (penW F N lam) hab k) →
            ∀ ℓ ∈ labels F hfin, Module.Finite (ZMod 2) (lensH D (nearOm M (U ℓ)) a b T k)) := by
  have hopen : ∀ ℓ ∈ labels F hfin, IsOpen (nearOm M (U ℓ)) :=
    fun ℓ hℓ => nearOm_isOpen M (hU ℓ hℓ).1
  have hdis' : ((labels F hfin : Finset (Set (Sphere n) × Bool)) :
      Set (Set (Sphere n) × Bool)).PairwiseDisjoint fun ℓ => nearOm M (U ℓ) :=
    fun ℓ hℓ ℓ' hℓ' hne => nearOm_disjoint M (hdis hℓ hℓ' hne)
  have hcrit : ∀ q : ZMod N → Sphere n, a₀ ^ 2 ≤ PolygonDescent.energy F N q →
      PolygonDescent.energy F N q ≤ b₀ ^ 2 → PolyCritical F N q →
      incl q ∈ ⋃ ℓ ∈ labels F hfin, nearOm M (U ℓ) := by
    intro q ha hb hc
    have h1 := broken_mem_crit M ha₀ hab₀ hone (hshort q hb) hc ha hb
    rw [crit_eq F c hfin] at h1
    obtain ⟨ℓ, hℓ, hmem⟩ := mem_iUnion₂.mp h1
    exact mem_iUnion₂.mpr ⟨ℓ, hℓ, incl_mem_nearOm M ⟨hshort q hb, (hU ℓ hℓ).2 hmem⟩⟩
  obtain ⟨D, hD⟩ := AmbientDescent.exists_descent F hn hlam hC hshort
    (isOpen_biUnion hopen) hcrit
  obtain ⟨d, hd, h⟩ := exists_family_decomposition D (penW_continuous F hn (N := N) lam)
    (AmbientPenalty.band_isCompact F hn hlam (a₀ ^ 2) (b₀ ^ 2)) (labels F hfin) hopen hdis' hD
  exact ⟨D, d, hd, h⟩

end

end Finsler.AmbientLoopPairs
