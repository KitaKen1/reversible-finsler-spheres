module

public import Finsler.Geometry.LevelDescent
public import Finsler.Analysis.EquivariantLevelBuild
public import Finsler.Geometry.RootFieldRotation
public import Finsler.Topology.AmbientK

/-! A compatible finite family of ambient labels gives a K-equivariant global descent.
The field agrees with every local split field on its tube and decreases the deformed energy
strictly off the label critical sets throughout the original penalized band. -/

@[expose] public section

namespace Finsler.LevelDescentK

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonDescent Finsler.PolygonLoop
open Finsler.PolygonCritical Finsler.PolygonSmooth Finsler.EnergySphereSmooth
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.LevelDescent Finsler.LevelField
open Finsler.EquivariantLevelBuild Finsler.AmbientK Finsler.AmbientSymmetry
open Finsler.PolygonDescentK Finsler.RevLabel Finsler.SampleK Finsler.RootFieldRotation
open scoped ContDiff NNReal
noncomputable section

variable {n : ℕ} (M : ℕ) [NeZero M]

theorem exists_level_descent_K (F : ReversibleMetric n) (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod (2 * M) → Sphere n,
      PolygonDescent.energy F (2 * M) q ≤ b₀ → ShortPolygon δ q)
    {ι : Type*} [Fintype ι] (rev : ι → ι)
    {U : ι → Set (ZMod (2 * M) → Ambient n)}
    {W : ι → (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n}
    {β : ι → (ZMod (2 * M) → Ambient n) → ℝ}
    {C T : ι → Set (ZMod (2 * M) → Ambient n)}
    (hU : ∀ i, IsOpen (U i)) (hUO : ∀ i, U i ⊆ regSet F (2 * M) 1)
    (hUdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hW : ∀ i, ContDiffOn ℝ ∞ (W i) (U i))
    (hWle : ∀ i, ∀ y ∈ U i, fderiv ℝ (pen F (2 * M) 1) y (W i y) ≤ 0)
    (hWlt : ∀ i, ∀ y ∈ U i, y ∉ C i → fderiv ℝ (pen F (2 * M) 1) y (W i y) < 0)
    (hT : ∀ i, IsCompact (T i)) (hTU : ∀ i, T i ⊆ U i)
    (hTr : ∀ i x, x ∈ T i → revA (2 * M) x ∈ T (rev i))
    (hTh : ∀ i x, x ∈ T i → rotA (2 * M) (M : ZMod (2 * M)) x ∈ T i)
    (hWr : ∀ i x, x ∈ T i → W (rev i) (revA (2 * M) x) = revA (2 * M) (W i x))
    (hWh : ∀ i x, x ∈ T i → W i (rotA (2 * M) (M : ZMod (2 * M)) x) =
      rotA (2 * M) (M : ZMod (2 * M)) (W i x))
    (hβT : ∀ i, tsupport (β i) ⊆ T i) (hβd : ∀ i y, DifferentiableAt ℝ (β i) y)
    (hβr : ∀ x, (∑ i, β i (revA (2 * M) x)) = ∑ i, β i x)
    (hβh : ∀ x, (∑ i, β i (rotA (2 * M) (M : ZMod (2 * M)) x)) = ∑ i, β i x)
    (hβle : ∀ i, ∀ y ∈ tsupport (β i),
      fderiv ℝ (fun y => pen F (2 * M) 1 y + β i y) y (W i y) ≤ 0)
    (hβlt : ∀ i, ∀ y ∈ tsupport (β i), y ∉ C i →
      fderiv ℝ (fun y => pen F (2 * M) 1 y + β i y) y (W i y) < 0)
    (hcrit : ∀ q : ZMod (2 * M) → Sphere n, a₀ ≤ PolygonDescent.energy F (2 * M) q →
      PolygonDescent.energy F (2 * M) q ≤ b₀ → PolyCritical F (2 * M) q →
        (incl q : Om n (2 * M)).1 ∈ ⋃ i, T i) :
    ∃ (V : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n) (KL : ℝ≥0)
      (hL : LipschitzWith KL V)
      (hV0 : ∀ P : ZMod (2 * M) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
      (hg : ∀ P ∈ regSet F (2 * M) 1,
        DifferentiableAt ℝ (fun y => pen F (2 * M) 1 y + ∑ j, β j y) P)
      (hsupp : ∀ P, V P ≠ 0 → P ∈ regSet F (2 * M) 1)
      (hle : ∀ P ∈ regSet F (2 * M) 1,
        fderiv ℝ (fun y => pen F (2 * M) 1 y + ∑ j, β j y) P (V P) ≤ 0),
      (∀ i, ∀ y ∈ T i, V y = W i y) ∧
      (∀ t Q, (descentOf hL hV0 hg hsupp hle).flow t ((ambK M).ρ Q) =
        (ambK M).ρ ((descentOf hL hV0 hg hsupp hle).flow t Q)) ∧
      (∀ t Q, (descentOf hL hV0 hg hsupp hle).flow t ((ambK M).σ Q) =
        (ambK M).σ ((descentOf hL hV0 hg hsupp hle).flow t Q)) ∧
      ∀ Q : Om n (2 * M), a₀ ≤ penW F (2 * M) 1 Q → penW F (2 * M) 1 Q ≤ b₀ →
        (∀ i, Q.1 ∉ C i) →
        pen F (2 * M) 1 ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 +
            ∑ j, β j ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 <
          pen F (2 * M) 1 Q.1 + ∑ j, β j Q.1 := by
  classical
  set B : Set (ZMod (2 * M) → Ambient n) :=
    {y | (∀ j, y j ≠ 0) ∧ a₀ ≤ pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y ≤ b₀}
  set Crit : Set (ZMod (2 * M) → Ambient n) := {y | ∃ q : ZMod (2 * M) → Sphere n,
    a₀ ≤ PolygonDescent.energy F (2 * M) q ∧ PolygonDescent.energy F (2 * M) q ≤ b₀ ∧
    PolyCritical F (2 * M) q ∧ (incl q : Om n (2 * M)).1 = y}
  have hcrit' : Crit ⊆ ⋃ i, T i := by
    rintro y ⟨q, h1, h2, h3, rfl⟩
    exact hcrit q h1 h2 h3
  have hband : ∀ 𝒲 : Set (ZMod (2 * M) → Ambient n), IsOpen 𝒲 → Crit ⊆ 𝒲 →
      ∃ V : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n,
        ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ regSet F (2 * M) 1 ∧
        (∀ y ∈ regSet F (2 * M) 1, fderiv ℝ (pen F (2 * M) 1) y (V y) ≤ 0) ∧
        ∀ y ∈ B, y ∉ 𝒲 → fderiv ℝ (pen F (2 * M) 1) y (V y) < 0 := by
    intro 𝒲 h𝒲 hC𝒲
    obtain ⟨V, hV, hVc, hVt, hVle, hVlt⟩ := exists_band_field F hn one_pos hδ hshort
      (h𝒲.preimage continuous_subtype_val) (fun q h1 h2 h3 => hC𝒲 ⟨q, h1, h2, h3, rfl⟩)
    exact ⟨V, hV, hVc, hVt, hVle, fun y hy hy𝒲 => hVlt ⟨y, hy.1⟩ hy.2.1 hy.2.2 hy𝒲⟩
  obtain ⟨V, hV, hVc, hVO, hVT, hVr, hVh, hVle, hVlt⟩ :=
    exists_equivariant_level_field (revA (2 * M)) (rotA (2 * M) (M : ZMod (2 * M)))
      (revA_revA _) (rotA_involutive (half_shift M)) (revA_rotA (half_shift M)) rev
      (fun x => pen_revA F 1 x) (fun x => pen_rotA (2 * M) F 1 _ x)
      (fun _ hx => regSet_revA F 1 hx) (fun _ hx => regSet_rotA F 1 _ hx)
      (fun _ hx => hx.2.differentiableAt one_ne_zero) hβr hβh
      hU hUO hUdis hW hWle hWlt hT hTU hTr hTh hWr hWh hβT hβd hβle hβlt hcrit' hband
  obtain ⟨KL, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  have hsupp : ∀ P, V P ≠ 0 → P ∈ regSet F (2 * M) 1 :=
    fun P hP => hVO (subset_tsupport V hP)
  have hV0 : ∀ P : ZMod (2 * M) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0 :=
    fun P hP => (hsupp P hP).1
  have hg : ∀ P ∈ regSet F (2 * M) 1,
      DifferentiableAt ℝ (fun y => pen F (2 * M) 1 y + ∑ j, β j y) P := fun P hP =>
    (hP.2.differentiableAt one_ne_zero).add (DifferentiableAt.fun_sum fun j _ => hβd j P)
  obtain ⟨hρ, hσ⟩ := descentOf_equivariant hL hV0 hg hsupp hVle hVr hVh
  refine ⟨V, KL, hL, hV0, hg, hsupp, hVle, hVT, hρ, hσ, fun Q ha hb hC => ?_⟩
  exact descentOf_lt hL hV0 hg hsupp hVle Q
    (hVlt Q.1 (band_regular F one_pos hδ hshort Q hb) ⟨Q.2, ha, hb⟩ hC)

end

end Finsler.LevelDescentK
