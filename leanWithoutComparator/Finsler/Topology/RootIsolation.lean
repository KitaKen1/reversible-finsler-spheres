module

public import Finsler.Topology.AmbientLoopPairs
public import Finsler.Geometry.LevelField
public import Finsler.Geometry.PolygonSampling

/-! The isolation of the sampled critical circles. For a polygon model with N vertices of a band
around the only critical level c, the samples of the loops of a set S of loops form a compact set
if S is compact, and lie in the regular set of the penalized energy if they are short. A
stationary polygon of the band is the polygon of samples of its broken geodesic, which lies in
the critical circle of some label; so the stationary polygons of the band lie in the union of the
sampled critical circles. If the samples of the loops of the critical circle of a label are short
with broken geodesics these loops, the sampled circle has an open neighbourhood in which every
critical point of the penalized energy (any nonzero weight) lies in the sampled circle: the
polygons with nonzero vertices whose normalization lies near an open neighbourhood of the circle
avoiding the other circles, with energy strictly inside the band. -/

@[expose] public section

namespace Finsler.RootIsolation

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonModel Finsler.PolygonDescent
open Finsler.PolygonCrossing Finsler.CriticalLevels Finsler.OrientedCritical
open Finsler.PolygonOriented Finsler.CriticalCircles Finsler.AmbientLoopPairs
open Finsler.PolygonSampling Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.LevelField
open Finsler.EnergyDiagonal Finsler.PolygonSmooth
open Set

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {A : ℝ} {N : ℕ} [NeZero N]

/-- The polygons with nonzero vertices form an open set. -/
theorem isOpen_nonzero : IsOpen {Q : ZMod N → Ambient n | ∀ j, Q j ≠ 0} := by
  have he : {Q : ZMod N → Ambient n | ∀ j, Q j ≠ 0} =
      ⋂ j, (fun Q : ZMod N → Ambient n => Q j) ⁻¹' ({0}ᶜ : Set (Ambient n)) := by
    ext Q
    simp
  rw [he]
  exact isOpen_iInter_of_finite fun j => isOpen_compl_singleton.preimage (continuous_apply j)

/-- The ambient samples of the loops of a set. -/
def sampleSet (N : ℕ) (S : Set (SphereLoop n)) : Set (ZMod N → Ambient n) :=
  (fun u => amb (samplePoly N u)) '' S

omit [NeZero N] in
theorem sampleSet_isCompact {S : Set (SphereLoop n)} (hS : IsCompact S) :
    IsCompact (sampleSet N S) :=
  hS.image ((amb_continuous N).comp (samplePoly_continuous N))

/-- Short samples are regular points of the penalized energy. -/
theorem sampleSet_subset_regSet {δ : ℝ}
    (hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {S : Set (SphereLoop n)} (hS : ∀ u ∈ S, ShortPolygon δ (samplePoly N u)) (lam : ℝ) :
    sampleSet N S ⊆ regSet F N lam := by
  rintro _ ⟨u, hu, rfl⟩
  have h := pen_contDiffAt_one F lam (incl (samplePoly N u))
    (polyEnergyN_contDiffAt F (incl (samplePoly N u)) (by
      rw [normalizeP_incl]
      exact polyEnergyN_contDiffAt_one F hC (hS u hu)))
  exact ⟨(incl (samplePoly N u)).2, h⟩

variable (M : PolygonModelData F A N)

/-- **Stationary polygons of the band are sampled critical loops.** -/
theorem crit_mem_sampleSet (hfin : (primeImages F).Finite) {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (hab₀ : a₀ ≤ b₀) (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ ^ 2 →
      ShortPolygon M.δ q)
    {q : ZMod N → Sphere n} (hc : PolyCritical F N q) (ha : a₀ ^ 2 ≤ PolygonDescent.energy F N q)
    (hb : PolygonDescent.energy F N q ≤ b₀ ^ 2) :
    ∃ ℓ ∈ labels F hfin, broken M ⟨q, hshort q hb⟩ ∈ circle F c ℓ ∧
      amb q ∈ sampleSet N (circle F c ℓ) := by
  have h1 := broken_mem_crit M ha₀ hab₀ hone (hshort q hb) hc ha hb
  rw [crit_eq F c hfin] at h1
  obtain ⟨ℓ, hℓ, hmem⟩ := mem_iUnion₂.mp h1
  refine ⟨ℓ, hℓ, hmem, ⟨_, hmem, ?_⟩⟩
  change amb (samplePoly N (broken M ⟨q, hshort q hb⟩)) = amb q
  rw [sample_broken M]

/-- **The isolation of a sampled critical circle.** -/
theorem exists_isolation (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < M.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hac : a₀ < c) (hcb : c < b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c)
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ ^ 2 →
      ShortPolygon M.δ q)
    {ℓ : Set (Sphere n) × Bool} (hℓ : ℓ ∈ labels F hfin)
    (hsamp : ∀ u ∈ circle F c ℓ, ∃ hq : ShortPolygon M.δ (samplePoly N u),
      broken M ⟨samplePoly N u, hq⟩ = u)
    (hE : ∀ u ∈ circle F c ℓ, SobolevEnergy.energy F u = c ^ 2) {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ 𝒱 : Set (ZMod N → Ambient n), IsOpen 𝒱 ∧ sampleSet N (circle F c ℓ) ⊆ 𝒱 ∧
      ∀ z ∈ 𝒱, fderiv ℝ (pen F N lam) z = 0 → z ∈ sampleSet N (circle F c ℓ) := by
  classical
  obtain ⟨U, hU, hUdis⟩ := exists_disjoint_nhds (labels F hfin) (circle F c)
    (fun ℓ' _ => isCompact_circle F c ℓ')
    (fun ℓ₁ _ ℓ₂ _ hne => circle_disjoint F c hne)
  have hab₀ : a₀ ≤ b₀ := (hac.trans hcb).le
  set W : Set (Om n N) := {Q | normalizeP Q ∈ near M (U ℓ) ∧
    a₀ ^ 2 < PolygonDescent.energy F N (normalizeP Q) ∧
      PolygonDescent.energy F N (normalizeP Q) < b₀ ^ 2} with hWdef
  have hW : IsOpen W := by
    have hE' : Continuous fun Q : Om n N => PolygonDescent.energy F N (normalizeP Q) :=
      (PolygonDescent.energy_continuous F hn N).comp normalizeP.continuous
    exact ((near_isOpen M (hU ℓ hℓ).1).preimage normalizeP.continuous).inter
      ((isOpen_lt continuous_const hE').inter (isOpen_lt hE' continuous_const))
  refine ⟨Subtype.val '' W, (isOpen_nonzero (N := N)).isOpenMap_subtype_val W hW, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hq, hbr⟩ := hsamp u hu
    refine ⟨incl (samplePoly N u), ⟨?_, ?_, ?_⟩, rfl⟩
    · rw [normalizeP_incl]
      refine ⟨hq, ?_⟩
      rw [hbr]
      exact (hU ℓ hℓ).2 hu
    · rw [normalizeP_incl]
      have h := energy_broken M ⟨samplePoly N u, hq⟩
      rw [hbr, hE u hu] at h
      have h' : polyEnergy F N (amb (samplePoly N u)) = c ^ 2 := h.symm
      change a₀ ^ 2 < polyEnergy F N (amb (samplePoly N u))
      rw [h']
      exact pow_lt_pow_left₀ hac ha₀.le two_ne_zero
    · rw [normalizeP_incl]
      have h := energy_broken M ⟨samplePoly N u, hq⟩
      rw [hbr, hE u hu] at h
      have h' : polyEnergy F N (amb (samplePoly N u)) = c ^ 2 := h.symm
      change polyEnergy F N (amb (samplePoly N u)) < b₀ ^ 2
      rw [h']
      exact pow_lt_pow_left₀ hcb (ha₀.le.trans hac.le) two_ne_zero
  · rintro _ ⟨Q, ⟨⟨hq, hbrU⟩, ha, hb⟩, rfl⟩ h0
    have hEd : DifferentiableAt ℝ (polyEnergyN F N) Q.1 :=
      (polyEnergyN_contDiffAt F Q (polyEnergyN_contDiffAt_one F hC hq)).differentiableAt
        one_ne_zero
    obtain ⟨hQ, hc⟩ := polyCritical_of_critical F hlam Q hEd h0
    obtain ⟨ℓ', hℓ', hmem, -⟩ := crit_mem_sampleSet M hfin ha₀ hab₀ hone hshort hc ha.le hb.le
    have hℓℓ : ℓ' = ℓ := by
      by_contra hne
      exact Set.disjoint_left.mp (hUdis hℓ' hℓ hne) ((hU ℓ' hℓ').2 hmem) hbrU
    subst hℓℓ
    refine ⟨_, hmem, ?_⟩
    change amb (samplePoly N (broken M ⟨normalizeP Q, _⟩)) = Q.1
    rw [sample_broken M]
    exact (congrArg Subtype.val hQ).symm

end

end Finsler.RootIsolation
