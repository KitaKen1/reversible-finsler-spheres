module

public import Finsler.Analysis.LevelBuild
public import Finsler.Geometry.LevelField

/-! The descent of a level. On the ambient polygons with K vertices, let finitely many labels be
given by pairwise disjoint open sets U_i of the regular set, fields W_i smooth on U_i along which
the penalized energy does not increase and decreases strictly off sets C_i, and differentiable
deformations β_i with closed supports in compact sets T_i ⊆ U_i along which pen + β_i does the
same, and let every stationary sphere polygon of a compact band lie in some T_i. Then there is a
Lipschitz field supported in the regular set, equal to W_i on T_i, whose descent decreases the
deformed energy pen + Σ β_i at every polygon of the band off the C_i in time one. -/

@[expose] public section

namespace Finsler.LevelDescent

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PolygonDescent
open Finsler.PseudoGradient Finsler.SphereFlow Finsler.FlowLens Finsler.AmbientPenalty
open Finsler.AmbientDescent Finsler.LevelField Finsler.LevelBuild
open Set Filter
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {K : ℕ} [NeZero K]

/-- Band polygons are regular points of the penalized energy. -/
theorem band_regular (F : ReversibleMetric n) {lam : ℝ} (hlam : 0 < lam) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {b₀ : ℝ}
    (hshort : ∀ q : ZMod K → Sphere n, PolygonDescent.energy F K q ≤ b₀ → ShortPolygon δ q)
    (Q : Om n K) (hb : penW F K lam Q ≤ b₀) : Q.1 ∈ regSet F K lam := by
  refine ⟨Q.2, ?_⟩
  have hle : PolygonDescent.energy F K (normalizeP Q) ≤ b₀ :=
    (energy_le_penW F hlam.le Q).trans hb
  exact pen_contDiffAt_one F lam Q (polyEnergyN_contDiffAt F Q
    (polyEnergyN_contDiffAt_one F hδ (hshort _ hle)))

/-- **The descent of a level.** -/
theorem exists_level_descent (F : ReversibleMetric n) (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod K → Sphere n, PolygonDescent.energy F K q ≤ b₀ → ShortPolygon δ q)
    {ι : Type*} (s : Finset ι) {U : ι → Set (ZMod K → Ambient n)}
    {W : ι → (ZMod K → Ambient n) → ZMod K → Ambient n}
    {β : ι → (ZMod K → Ambient n) → ℝ} {C T : ι → Set (ZMod K → Ambient n)}
    (hU : ∀ i ∈ s, IsOpen (U i)) (hUO : ∀ i ∈ s, U i ⊆ regSet F K 1)
    (hUdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (hW : ∀ i ∈ s, ContDiffOn ℝ ∞ (W i) (U i))
    (hWle : ∀ i ∈ s, ∀ y ∈ U i, fderiv ℝ (pen F K 1) y (W i y) ≤ 0)
    (hWlt : ∀ i ∈ s, ∀ y ∈ U i, y ∉ C i → fderiv ℝ (pen F K 1) y (W i y) < 0)
    (hT : ∀ i ∈ s, IsCompact (T i)) (hTU : ∀ i ∈ s, T i ⊆ U i)
    (hβT : ∀ i ∈ s, tsupport (β i) ⊆ T i) (hβd : ∀ i ∈ s, ∀ y, DifferentiableAt ℝ (β i) y)
    (hβle : ∀ i ∈ s, ∀ y ∈ tsupport (β i),
      fderiv ℝ (fun y => pen F K 1 y + β i y) y (W i y) ≤ 0)
    (hβlt : ∀ i ∈ s, ∀ y ∈ tsupport (β i), y ∉ C i →
      fderiv ℝ (fun y => pen F K 1 y + β i y) y (W i y) < 0)
    (hcrit : ∀ q : ZMod K → Sphere n, a₀ ≤ PolygonDescent.energy F K q →
      PolygonDescent.energy F K q ≤ b₀ → PolyCritical F K q →
        (incl q : Om n K).1 ∈ ⋃ i ∈ s, T i) :
    ∃ (V : (ZMod K → Ambient n) → ZMod K → Ambient n) (KL : ℝ≥0) (hL : LipschitzWith KL V)
      (hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
      (hg : ∀ P ∈ regSet F K 1,
        DifferentiableAt ℝ (fun y => pen F K 1 y + ∑ j ∈ s, β j y) P)
      (hsupp : ∀ P, V P ≠ 0 → P ∈ regSet F K 1)
      (hle : ∀ P ∈ regSet F K 1,
        fderiv ℝ (fun y => pen F K 1 y + ∑ j ∈ s, β j y) P (V P) ≤ 0),
      (∀ i ∈ s, ∀ y ∈ T i, V y = W i y) ∧
      ∀ Q : Om n K, a₀ ≤ penW F K 1 Q → penW F K 1 Q ≤ b₀ → (∀ i ∈ s, Q.1 ∉ C i) →
        pen F K 1 ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 +
            ∑ j ∈ s, β j ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 <
          pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 := by
  classical
  set B : Set (ZMod K → Ambient n) := {y | (∀ j, y j ≠ 0) ∧ a₀ ≤ pen F K 1 y ∧ pen F K 1 y ≤ b₀}
    with hBdef
  set Crit : Set (ZMod K → Ambient n) := {y | ∃ q : ZMod K → Sphere n,
    a₀ ≤ PolygonDescent.energy F K q ∧ PolygonDescent.energy F K q ≤ b₀ ∧ PolyCritical F K q ∧
      (incl q : Om n K).1 = y} with hCritdef
  have hcrit' : Crit ⊆ ⋃ i ∈ s, T i := by
    rintro y ⟨q, h1, h2, h3, rfl⟩
    exact hcrit q h1 h2 h3
  have hband : ∀ 𝒲 : Set (ZMod K → Ambient n), IsOpen 𝒲 → Crit ⊆ 𝒲 →
      ∃ V : (ZMod K → Ambient n) → ZMod K → Ambient n, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
        tsupport V ⊆ regSet F K 1 ∧ (∀ y ∈ regSet F K 1, fderiv ℝ (pen F K 1) y (V y) ≤ 0) ∧
        ∀ y ∈ B, y ∉ 𝒲 → fderiv ℝ (pen F K 1) y (V y) < 0 := by
    intro 𝒲 h𝒲 hC𝒲
    have h𝒲' : IsOpen {Q : Om n K | Q.1 ∈ 𝒲} := h𝒲.preimage continuous_subtype_val
    obtain ⟨V, hV, hVc, hVt, hVle, hVlt⟩ := exists_band_field F hn one_pos hδ hshort h𝒲'
      (fun q h1 h2 h3 => hC𝒲 ⟨q, h1, h2, h3, rfl⟩)
    refine ⟨V, hV, hVc, hVt, hVle, fun y hy hy𝒲 => ?_⟩
    exact hVlt ⟨y, hy.1⟩ hy.2.1 hy.2.2 hy𝒲
  obtain ⟨V, hV, hVc, hVt, hVT, hVle, hVlt⟩ := exists_level_field s (f := pen F K 1)
    (O := regSet F K 1) (B := B) hU hUO hUdis hW hWle hWlt hT hTU hβT hβle hβlt hcrit' hband
  obtain ⟨KL, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  have hsupp : ∀ P, V P ≠ 0 → P ∈ regSet F K 1 := fun P hP => hVt (subset_tsupport V hP)
  have hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0 := fun P hP => (hsupp P hP).1
  have hg : ∀ P ∈ regSet F K 1,
      DifferentiableAt ℝ (fun y => pen F K 1 y + ∑ j ∈ s, β j y) P := by
    intro P hP
    have h1 : DifferentiableAt ℝ (pen F K 1) P := hP.2.differentiableAt one_ne_zero
    have h2 : DifferentiableAt ℝ (fun y => ∑ j ∈ s, β j y) P :=
      DifferentiableAt.fun_sum fun j hj => hβd j hj P
    exact h1.add h2
  refine ⟨V, KL, hL, hV0, hg, hsupp, hVle, hVT, fun Q ha hb hC => ?_⟩
  have hreg := band_regular F one_pos hδ hshort Q hb
  have hlt := hVlt Q.1 hreg ⟨Q.2, ha, hb⟩ hC
  exact descentOf_lt hL hV0 hg hsupp hVle Q hlt

end

end Finsler.LevelDescent
