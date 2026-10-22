module

public import Finsler.Geometry.AmbientDescent
public import Finsler.Analysis.GlueField

/-! Descent fields of the penalized energy on a band, as fields. The regular set of the
penalized energy consists of the ambient polygons with nonzero vertices at which the penalized
energy is C¹; it is open. For a compact band of the penalized energy and an open set 𝒲 of
polygons with nonzero vertices containing the stationary sphere polygons of the band, there is
a smooth compactly supported field supported in the regular set along which the penalized
energy does not increase, and decreases strictly at the polygons of the band outside 𝒲. This
is the field behind the descent of v0.109, kept as a field so that it can be glued with the
split fields near the critical circles; its descent is obtained from the field by the
construction of v0.109. -/

@[expose] public section

namespace Finsler.LevelField

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PolygonDescent
open Finsler.PseudoGradient Finsler.SphereFlow Finsler.FlowLens Finsler.AmbientPenalty
open Finsler.AmbientDescent
open Set Filter
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-- The regular set of the penalized energy: ambient polygons with nonzero vertices at which the
penalized energy is C¹. -/
def regSet (F : ReversibleMetric n) (N : ℕ) [NeZero N] (lam : ℝ) : Set (ZMod N → Ambient n) :=
  {Q | (∀ j, Q j ≠ 0) ∧ ContDiffAt ℝ 1 (pen F N lam) Q}

theorem regSet_isOpen (F : ReversibleMetric n) (lam : ℝ) : IsOpen (regSet F N lam) := by
  have h1 : IsOpen {Q : ZMod N → Ambient n | ∀ j, Q j ≠ 0} := by
    have he : {Q : ZMod N → Ambient n | ∀ j, Q j ≠ 0} =
        ⋂ j, (fun Q : ZMod N → Ambient n => Q j) ⁻¹' {y | y ≠ 0} := by
      ext Q
      simp
    rw [he]
    exact isOpen_iInter_of_finite fun j => isOpen_ne.preimage (continuous_apply j)
  have h2 : IsOpen {Q : ZMod N → Ambient n | ContDiffAt ℝ 1 (pen F N lam) Q} := by
    rw [isOpen_iff_mem_nhds]
    intro Q hQ
    exact ContDiffAt.eventually (show ContDiffAt ℝ 1 (pen F N lam) Q from hQ) (by simp)
  exact h1.inter h2

/-- **A descent field of the penalized energy on a band.** For a compact band of the penalized
energy and an open set 𝒲 containing the stationary sphere polygons of the band, there is a
smooth compactly supported field supported in the regular set, along which the penalized
energy does not increase on the regular set and decreases strictly at the polygons of the band
outside 𝒲. -/
theorem exists_band_field (F : ReversibleMetric n) (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ → ShortPolygon δ q)
    {𝒲 : Set (Om n N)} (h𝒲 : IsOpen 𝒲)
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ PolygonDescent.energy F N q →
      PolygonDescent.energy F N q ≤ b₀ → PolyCritical F N q → incl q ∈ 𝒲) :
    ∃ V : (ZMod N → Ambient n) → ZMod N → Ambient n, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      tsupport V ⊆ regSet F N lam ∧
      (∀ P ∈ regSet F N lam, fderiv ℝ (pen F N lam) P (V P) ≤ 0) ∧
      ∀ Q : Om n N, a₀ ≤ penW F N lam Q → penW F N lam Q ≤ b₀ → Q ∉ 𝒲 →
        fderiv ℝ (pen F N lam) Q.1 (V Q.1) < 0 := by
  have hO := regSet_isOpen (N := N) F lam
  have hfO : ContDiffOn ℝ 1 (pen F N lam) (regSet F N lam) := fun Q hQ =>
    hQ.2.contDiffWithinAt
  have hcont := penW_continuous F hn (N := N) lam
  set C : Set (Om n N) := {Q | a₀ ≤ penW F N lam Q ∧ penW F N lam Q ≤ b₀} ∩ 𝒲ᶜ with hCdef
  have hCc : IsCompact C :=
    (band_isCompact F hn hlam a₀ b₀).inter_right h𝒲.isClosed_compl
  have hA : IsCompact (Subtype.val '' C) := hCc.image continuous_subtype_val
  have hEreg : ∀ Q : Om n N, penW F N lam Q ≤ b₀ → ContDiffAt ℝ 1 (polyEnergyN F N) Q.1 := by
    intro Q hQ
    have hle : PolygonDescent.energy F N (normalizeP Q) ≤ b₀ :=
      (energy_le_penW F hlam.le Q).trans hQ
    exact polyEnergyN_contDiffAt F Q (polyEnergyN_contDiffAt_one F hδ (hshort _ hle))
  have hAO : Subtype.val '' C ⊆ regSet F N lam := by
    rintro _ ⟨Q, hQ, rfl⟩
    exact ⟨Q.2, pen_contDiffAt_one F lam Q (hEreg Q hQ.1.2)⟩
  have hne : ∀ P ∈ Subtype.val '' C, fderiv ℝ (pen F N lam) P ≠ 0 := by
    rintro _ ⟨Q, hQ, rfl⟩ h0
    have hE := (hEreg Q hQ.1.2).differentiableAt one_ne_zero
    obtain ⟨hQeq, hpc⟩ := polyCritical_of_critical F hlam.ne' Q hE h0
    have hen : penW F N lam Q = PolygonDescent.energy F N (normalizeP Q) := by
      conv_lhs => rw [hQeq]
      exact penW_incl F lam _
    apply hQ.2
    rw [hQeq]
    exact hcrit _ (hen ▸ hQ.1.1) (hen ▸ hQ.1.2) hpc
  obtain ⟨V, hVs, hVcs, hVt, hVle, hVlt⟩ := exists_pseudoGradient hO hfO hA hAO hne
  exact ⟨V, hVs, hVcs, hVt, hVle, fun Q ha hb hQ => hVlt _ ⟨Q, ⟨⟨ha, hb⟩, hQ⟩, rfl⟩⟩

/-- A smooth compactly supported field supported in the regular set gives a descent of the
penalized energy on the polygons with nonzero vertices if the penalized energy does not
increase along it; its time-one map decreases the penalized energy strictly where the
derivative along the field is negative. -/
theorem exists_descent_of_field (F : ReversibleMetric n) {lam : ℝ}
    {V : (ZMod N → Ambient n) → ZMod N → Ambient n} (hVs : ContDiff ℝ ∞ V)
    (hVcs : HasCompactSupport V) (hVt : tsupport V ⊆ regSet F N lam)
    (hVle : ∀ P ∈ regSet F N lam, fderiv ℝ (pen F N lam) P (V P) ≤ 0) :
    ∃ D : Descent (Om n N) (penW F N lam), ∀ Q : Om n N,
      fderiv ℝ (pen F N lam) Q.1 (V Q.1) < 0 → penW F N lam (D.flow 1 Q) < penW F N lam Q := by
  obtain ⟨K, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVcs hVs (by simp)
  have hsupp : ∀ P, V P ≠ 0 → P ∈ regSet F N lam := fun P hP => hVt (subset_tsupport V hP)
  have hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0 := fun P hP => (hsupp P hP).1
  have hdiff : ∀ P ∈ regSet F N lam, DifferentiableAt ℝ (pen F N lam) P := fun P hP =>
    hP.2.differentiableAt one_ne_zero
  exact ⟨descentOf hL hV0 hdiff hsupp hVle, fun Q hQ =>
    descentOf_lt hL hV0 hdiff hsupp hVle Q hQ⟩

end

end Finsler.LevelField
