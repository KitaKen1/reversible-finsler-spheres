module

public import Finsler.Geometry.LabelPackBase
public import Finsler.Geometry.RootTubeData
public import Finsler.Geometry.LabelModelAgreement
public import Finsler.Geometry.RootField
public import Finsler.Geometry.InvariantLabelChoice
public import Finsler.Geometry.LabelRegionRotation
public import Finsler.Geometry.LabelSetRotation
public import Finsler.Geometry.RootFieldRotation

/-! Ordinary half-equivariant labels and retained root data constructed with the same
actual field, nested neighbourhoods, fibre radius, coordinate region and deformation. -/

@[expose] public section

namespace Finsler.LabelPackRoot

open Finsler.LabelPack Finsler.LabelRootData
open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.NormalFamily
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform Finsler.LabelTransport
open Finsler.LabelRegions Finsler.LabelData Finsler.LabelLevel Finsler.LevelField
open Finsler.LabelRegion Finsler.AmbientDescent Finsler.FlowLens Finsler.LogCutoff
open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LensContinuation Finsler.ProductModel
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {m N : ℕ} [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  {G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m}
  {G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m}


def SharedRoot (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (a : ZMod (m * N)) (Γ : Set (ZMod N → Ambient n)) (Wrest : Set (Om n N))
    (a₀ b₀ c₀ : ℝ) (𝒰 : Set (ZMod (m * N) → Ambient n))
    (U : Set (ZMod (m * N) → Ambient n))
    (W : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n)
    (β : (ZMod (m * N) → Ambient n) → ℝ) (T : Set (ZMod (m * N) → Ambient n))
    (𝒲 𝒲' : Set (Om n (m * N))) (Z₀ : Set (ZMod N → Ambient n))
    (ψ₀ : Descent (Om n N) (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)) : Prop :=
  ∃ B : RootTubeData F (G₁ := G₁) (G₂ := G₂) ψ a Γ Wrest a₀ b₀ c₀ 𝒰,
    B.Z₀ = Z₀ ∧ ψ₀ = descentOf B.lipschitz B.nonzero B.diff B.supp B.nonpos ∧
    B.U ⊆ T ∧ B.U ⊆ U ∧
    (∀ Q, W Q = splitW m N G₁ G₂ ψ B.V Q) ∧
    𝒲 = labelSetA m N G₁ G₂ ψ B.Z₀ B.U B.ρ ∧
    𝒲' = labelSetA m N G₁ G₂ ψ B.Z B.U (B.ρ / Real.exp 1) ∧
    ∀ Q ∈ 𝒲, pen F (m * N) 1 Q.1 + β Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1)

set_option maxHeartbeats 2400000 in
theorem label_pack_half_root (hn : 1 ≤ n) (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (a : ZMod (m * N)) (ha : a + a = 0) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z i, G₁ (rotA N (red m N a) z) i = d₁ i • rotV m N a (G₁ z i))
    (h₂ : ∀ z i, G₂ (rotA N (red m N a) z) i = d₂ i • rotV m N a (G₂ z i))
    {𝒪 : Set (ZMod N → Ambient n)} (h𝒪 : IsOpen 𝒪) (h𝒪s : 𝒪 ⊆ smoothSet m N F)
    (hneg : ∀ z ∈ 𝒪, Neg (normalForm m N F z) (G₁ z) ∧ Neg (-normalForm m N F z) (G₂ z))
    (h𝒪nz : ∀ z ∈ 𝒪, ∀ j, z j ≠ 0)
    {Γ : Set (ZMod N → Ambient n)} (hΓ : IsCompact Γ) (hΓ𝒪 : Γ ⊆ 𝒪)
    (hΓτ : ∀ z ∈ Γ, rotA N (red m N a) z ∈ Γ)
    (hiso : ∀ z ∈ 𝒪, fderiv ℝ (pen F N (1 / m)) z = 0 → z ∈ Γ)
    {a₀ b₀ : ℝ}
    (hΓval : ∀ z ∈ Γ, a₀ < (m : ℝ) ^ 2 * pen F N (1 / m) z ∧ (m : ℝ) ^ 2 * pen F N (1 / m) z < b₀)
    (hroot : ∀ κ : ℝ, 0 < κ → ∃ V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n,
      ContDiff ℝ ∞ V₀ ∧ HasCompactSupport V₀ ∧ tsupport V₀ ⊆ regSet F N (1 / m) ∧
      (∀ z, ‖V₀ z‖ ≤ κ) ∧
      (∀ z ∈ regSet F N (1 / m), fderiv ℝ (pen F N (1 / m)) z (V₀ z) ≤ 0) ∧
      ∀ z ∈ regSet F N (1 / m), a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z →
        (m : ℝ) ^ 2 * pen F N (1 / m) z ≤ b₀ → fderiv ℝ (pen F N (1 / m)) z ≠ 0 →
        fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0)
    (hKr : IsCompact {z : Om n N | a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀})
    (hbandreg : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → Q.1 ∈ regSet F N (1 / m))
    {Wrest : Set (Om n N)} (hWrest : IsOpen Wrest) {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hWΓ : ∀ Q ∈ Wrest, Q.1 ∉ thickening δ₁ Γ)
    (hrcrit : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → fderiv ℝ (pen F N (1 / m)) Q.1 = 0 →
        Q.1 ∈ Γ ∨ Q ∈ Wrest)
    {𝒰 : Set (ZMod (m * N) → Ambient n)} (h𝒰 : IsOpen 𝒰) (hΓ𝒰 : ∀ z ∈ Γ, reidx (rfl : m * N = m * N) (iterA m N z) ∈ 𝒰)
    {c₀ : ℝ} (ha₀c₀ : a₀ < c₀) (hc₀b₀ : c₀ < b₀)
    (hΓc₀ : ∀ z ∈ Γ, (m : ℝ) ^ 2 * pen F N (1 / m) z = c₀)
    (hrval : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → fderiv ℝ (pen F N (1 / m)) Q.1 = 0 →
        (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 = c₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ (U : Set (ZMod (m * N) → Ambient n))
      (W : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n)
      (β : (ZMod (m * N) → Ambient n) → ℝ) (C T : Set (ZMod (m * N) → Ambient n))
      (𝒲 𝒲' : Set (Om n (m * N))) (Z₀ : Set (ZMod N → Ambient n))
      (ψ₀ : Descent (Om n N) (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)),
      SharedRoot F (G₁ := G₁) (G₂ := G₂) ψ a Γ Wrest a₀ b₀ c₀ 𝒰 U W β T 𝒲 𝒲' Z₀ ψ₀ ∧
      (∀ y, rotA (m * N) a y ∈ U ↔ y ∈ U) ∧
      (∀ y, rotA (m * N) a y ∈ T ↔ y ∈ T) ∧
      (∀ y ∈ U, W (rotA (m * N) a y) = rotA (m * N) a (W y)) ∧
      (∀ y, β (rotA (m * N) a y) = β y) ∧
      (∀ Q, Finsler.LabelSetRotation.rotOm m N a Q ∈ 𝒲 ↔ Q ∈ 𝒲) ∧
      (∀ Q, Finsler.LabelSetRotation.rotOm m N a Q ∈ 𝒲' ↔ Q ∈ 𝒲') ∧
      (∀ z, rotA N (red m N a) z ∈ Z₀ ↔ z ∈ Z₀) ∧
      IsOpen U ∧ U ⊆ 𝒰 ∧ U ⊆ regSet F (m * N) 1 ∧ ContDiffOn ℝ ∞ W U ∧
      (∀ y ∈ U, fderiv ℝ (pen F (m * N) 1) y (W y) ≤ 0) ∧
      (∀ y ∈ U, y ∉ C → fderiv ℝ (pen F (m * N) 1) y (W y) < 0) ∧
      IsCompact T ∧ T ⊆ U ∧ tsupport β ⊆ T ∧ (∀ y, DifferentiableAt ℝ β y) ∧ (∀ y, |β y| ≤ η) ∧
      (∀ y ∈ tsupport β, fderiv ℝ (fun y => pen F (m * N) 1 y + β y) y (W y) ≤ 0) ∧
      (∀ y ∈ tsupport β, y ∉ C → fderiv ℝ (fun y => pen F (m * N) 1 y + β y) y (W y) < 0) ∧
      IsOpen 𝒲 ∧ IsOpen 𝒲' ∧ 𝒲' ⊆ 𝒲 ∧ (∀ Q ∈ 𝒲, Q.1 ∈ T) ∧
      (∀ Q : Om n (m * N), Q.1 ∈ C → Q ∈ 𝒲') ∧ (∀ z ∈ Γ, reidx (rfl : m * N = m * N) (iterA m N z) ∈ T) ∧
      (∀ y ∈ C, pen F (m * N) 1 y = c₀ ∧ β y = 0) ∧
      IsOpen {z : Om n N | z.1 ∈ Z₀} ∧ Disjoint {z : Om n N | z.1 ∈ Z₀} Wrest ∧
      (∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → z ∉ {z : Om n N | z.1 ∈ Z₀} ∪ Wrest →
        (m : ℝ) ^ 2 * pen F N (1 / m) (ψ₀.flow 1 z).1 < (m : ℝ) ^ 2 * pen F N (1 / m) z.1) ∧
      (∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≠ c₀ →
        (m : ℝ) ^ 2 * pen F N (1 / m) (ψ₀.flow 1 z).1 < (m : ℝ) ^ 2 * pen F N (1 / m) z.1) ∧
      ∀ {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {KL : ℝ≥0}
        (hL : LipschitzWith KL V) (hV0 : ∀ P : ZMod (m * N) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
        {g : (ZMod (m * N) → Ambient n) → ℝ} {O : Set (ZMod (m * N) → Ambient n)}
        (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
        (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0),
        (∀ y ∈ T, V y = W y) → (∀ y ∈ T, g y = pen F (m * N) 1 y + β y) →
        ∀ {a₀a b₀a : ℝ}, a₀a < c₀ → c₀ < b₀a → Continuous (fun Q : Om n (m * N) => g Q.1) →
        IsCompact {Q : Om n (m * N) | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a} →
        ∀ {R : Set (Om n (m * N))}, IsOpen R → Disjoint 𝒲 R →
        (∀ Q : Om n (m * N), a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ 𝒲' ∪ R →
          g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
        ∃ d : ℝ, 0 < d ∧ ∀ a c T : ℝ, 1 ≤ T → a < c₀ → c₀ < c → c - a < d →
          (∀ k : ℕ, Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
              (fun Q : Om n (m * N) => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c T))) (k + b)) =
            Module.finrank (ZMod 2) (H (triv (pairOf (inter_subset_left :
              baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1) {z : Om n N | z.1 ∈ Z₀} c ∩
                baseO ψ₀ a T ⊆
              baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)
                {z : Om n N | z.1 ∈ Z₀} c))) k)) ∧
          (∀ k : ℕ, k < b → ∀ x : H (triv (pairOf (partY_sub_partU
              (fun Q : Om n (m * N) => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c T))) k,
            x = 0) := by
  classical
  let τ := rotA (n := n) N (red m N a)
  have hred : red m N a + red m N a = 0 := by rw [← map_add, ha, map_zero]
  have hτ : ∀ z, τ (τ z) = z := Finsler.PolygonDescentK.rotA_involutive hred
  have hτiso : Isometry τ := by
    apply Isometry.of_dist_eq
    intro z z'
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact Finsler.RotationNatural.norm_rotA N (red m N a) (z - z')
  have hth : ∀ R z, τ z ∈ thickening R Γ ↔ z ∈ thickening R Γ :=
    Finsler.InvariantThickening.thickening_invariant τ hτ hΓτ hτiso
  have hcth : ∀ R z, τ z ∈ cthickening R Γ ↔ z ∈ cthickening R Γ :=
    Finsler.InvariantThickening.cthickening_invariant τ hτ hΓτ hτiso
  -- 𝒪 lies in the regular set of the root functional
  have h𝒪r : 𝒪 ⊆ regSet F N (1 / m) := fun z hz =>
    ⟨h𝒪nz z hz, (pen_root_contDiffAt m N F (h𝒪s hz)).of_le (by norm_num)⟩
  -- the open band set, kept away from Wrest
  obtain ⟨𝒪', h𝒪'o, hΓ𝒪', h𝒪'𝒪, h𝒪'val, h𝒪'𝒰⟩ :=
    exists_band_thickening F h𝒪 h𝒪r hΓ𝒪 hΓval h𝒰 hΓ𝒰
  have h𝒪₂ : IsOpen (𝒪' ∩ thickening δ₁ Γ) := h𝒪'o.inter isOpen_thickening
  have hΓ𝒪₂ : Γ ⊆ 𝒪' ∩ thickening δ₁ Γ := fun z hz =>
    ⟨hΓ𝒪' hz, self_subset_thickening hδ₁ Γ hz⟩
  have h𝒪₂𝒪 : 𝒪' ∩ thickening δ₁ Γ ⊆ 𝒪 := fun z hz => h𝒪'𝒪 hz.1
  -- the constants on K₀ = cthickening δ Γ
  obtain ⟨δ, R, κ, c, C₁, hδ, hR, hκ, hc, hC₁, hK₀sub, hest, hquad⟩ :=
    exists_label_constants m N F G₁ G₂ hG₁ hG₂ h𝒪₂ (h𝒪₂𝒪.trans h𝒪s)
      (fun z hz => hneg z (h𝒪₂𝒪 hz)) hΓ hΓ𝒪₂
  have hK₀c : IsCompact (cthickening δ Γ) := hΓ.cthickening
  have hK₀𝒪 : ∀ z ∈ cthickening δ Γ, z ∈ 𝒪 := fun z hz => h𝒪₂𝒪 (hK₀sub hz)
  have hK₀u : ∀ z ∈ cthickening δ Γ, IsUnit (matA m N G₁ G₂ ψ z) := fun z hz =>
    isUnit_of_neg m N F G₁ G₂ ψ (hneg z (hK₀𝒪 z hz))
  have hK₀nz : ∀ z ∈ cthickening δ Γ, ∀ j, z j ≠ 0 := fun z hz => h𝒪nz z (hK₀𝒪 z hz)
  have hK₀reg : cthickening δ Γ ⊆ regSet F N (1 / m) := fun z hz => h𝒪r (hK₀𝒪 z hz)
  have hK₀val : ∀ z ∈ cthickening δ Γ, a₀ < (m : ℝ) ^ 2 * pen F N (1 / m) z ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z < b₀ := fun z hz => h𝒪'val z (hK₀sub hz).1
  have hK₀δ₁ : cthickening δ Γ ⊆ thickening δ₁ Γ := fun z hz => (hK₀sub hz).2
  -- tubes: nonzero vertices and the open set 𝒰
  obtain ⟨Rnz, hRnz, hnzK⟩ := exists_nonzero_tube m N hG₁ hG₂ hK₀c hK₀nz
  have hpre : IsOpen (coord m N G₁ G₂ ⁻¹' 𝒰) :=
    h𝒰.preimage (coord_contDiff m N G₁ G₂ hG₁ hG₂).continuous
  obtain ⟨R𝒰, hR𝒰, h𝒰tube⟩ := Finsler.NormalExpansion.exists_tube hpre hK₀c
    (fun z hz => by
      change coord m N G₁ G₂ (z, 0) ∈ 𝒰
      rw [coord_zero]
      exact h𝒪'𝒰 z (hK₀sub hz).1)
  -- the radius R₂
  have hC₁1 : 0 < C₁ + 1 := by linarith only [hC₁]
  set Rη : ℝ := min 1 (η / (C₁ + 1)) with hRηdef
  have hRη : 0 < Rη := lt_min one_pos (by positivity)
  set R₂ : ℝ := min R (min Rnz (min R𝒰 Rη)) with hR₂def
  have hR₂ : 0 < R₂ := lt_min hR (lt_min hRnz (lt_min hR𝒰 hRη))
  have hR₂R : R₂ ≤ R := min_le_left _ _
  have hR₂nz : R₂ ≤ Rnz := (min_le_right _ _).trans (min_le_left _ _)
  have hR₂𝒰 : R₂ ≤ R𝒰 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hR₂η : R₂ ≤ Rη := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the cutoffs and the small constants
  obtain ⟨χ₀, W₀, B, M, lam, r, κ', hχ, hχ01, hχc, hχs, hχτ, hWτ, hW₀, hTW, hχ1, hB0, hB, hM, hlam, hr,
    hrR, hκ'0, hsmall⟩ := Finsler.InvariantLabelChoice.exists_invariant_label_choice
      τ hτ hτiso hΓτ hΓ (half_pos hδ) hR₂ hc hC₁ b p
  -- the sets and radii
  set R₁ : ℝ := R₂ / 2 with hR₁def
  set κ'' : ℝ := min κ' (min κ (δ / 32)) with hκ''def
  set ρ : ℝ := min R₁ (r / 2) with hρdef
  set ρ' : ℝ := ρ / Real.exp 1 with hρ'def
  have hκ'' : 0 < κ'' := lt_min hκ'0 (lt_min hκ (by positivity))
  have hR₁ : 0 < R₁ := half_pos hR₂
  have hρ : 0 < ρ := lt_min hR₁ (half_pos hr)
  have hR₁R₂ : R₁ < R₂ := half_lt_self hR₂
  have hR₁nz : R₁ ≤ Rnz := by rw [hR₁def]; linarith only [hR₂nz, hR₂]
  have hκ''κ' : κ'' ≤ κ' := min_le_left _ _
  have hκ''κ : κ'' ≤ κ := (min_le_right _ _).trans (min_le_left _ _)
  have hκ''δ : κ'' ≤ δ / 32 := (min_le_right _ _).trans (min_le_right _ _)
  have hρR₁ : ρ ≤ R₁ := min_le_left _ _
  have hρr2 : ρ ≤ r / 2 := min_le_right _ _
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith only [this]
  have hρ'ρ : ρ' ≤ ρ := div_le_self hρ.le he1
  have hρ'0 : 0 < ρ' := div_pos hρ (Real.exp_pos 1)
  have hρ'e : ρ' * Real.exp 1 ≤ ρ := le_of_eq (div_mul_cancel₀ ρ (Real.exp_pos 1).ne')
  have hrR₂ : r ^ 2 * Real.exp lam ≤ R₂ ^ 2 :=
    hrR.trans (by rw [hR₁def]; exact pow_le_pow_left₀ (by positivity) (half_le_self hR₂.le) 2)
  clear_value ρ' ρ κ'' R₁
  have hthK : thickening δ Γ ⊆ cthickening δ Γ := thickening_subset_cthickening δ Γ
  have hclZ₁ : closure (thickening (3 * δ / 4) Γ) ⊆ interior (cthickening δ Γ) := by
    have h1 : closure (thickening (3 * δ / 4) Γ) ⊆ cthickening (3 * δ / 4) Γ :=
      closure_thickening_subset_cthickening _ Γ
    have h2 : cthickening (3 * δ / 4) Γ ⊆ thickening δ Γ :=
      cthickening_subset_thickening' hδ (by linarith only [hδ]) Γ
    exact (h1.trans h2).trans (interior_maximal hthK isOpen_thickening)
  have hZ₁K : thickening (3 * δ / 4) Γ ⊆ cthickening δ Γ :=
    (thickening_mono (by linarith only [hδ]) Γ).trans hthK
  have hZ₀Z₁ : thickening (δ / 8) Γ ⊆ thickening (3 * δ / 4) Γ := thickening_mono (by linarith only [hδ]) Γ
  have hZ₀'Z₀ : thickening (δ / 16) Γ ⊆ thickening (δ / 8) Γ := thickening_mono (by linarith only [hδ]) Γ
  have hχZ : tsupport χ₀ ⊆ closure (thickening (3 * δ / 4) Γ) :=
    hχs.trans ((thickening_mono (by linarith only [hδ]) Γ).trans subset_closure)
  have hχ1Z₀ : ∀ z ∈ thickening (δ / 8) Γ, χ₀ z = 1 := fun z hz =>
    hχ1 z (hTW (thickening_subset_cthickening _ Γ (thickening_mono (by linarith only [hδ]) Γ hz)))
  -- the root field
  obtain ⟨Vraw, hraw, hrawc, hrawt, hrawb, hrawle, hrawlt⟩ := hroot κ'' hκ''
  let V₀ := Finsler.EquivariantApprox.average τ τ Vraw
  obtain ⟨hV₀, hV₀c, hV₀t, hV₀b, hV₀le, hV₀τ, hstrict⟩ :=
    Finsler.RootFieldRotation.average_root_field F (1 / m) (red m N a) hred
      hraw hrawc hrawt hrawb hrawle
  have hV₀lt : ∀ z ∈ regSet F N (1 / m), a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z →
      (m : ℝ) ^ 2 * pen F N (1 / m) z ≤ b₀ → fderiv ℝ (pen F N (1 / m)) z ≠ 0 →
      fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0 :=
    fun z hz hza hzb hne => hstrict z (hrawlt z hz hza hzb hne)
  obtain ⟨K₀', hL₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hV₀c hV₀ (by simp)
  have hsupp₀ : ∀ z, V₀ z ≠ 0 → z ∈ regSet F N (1 / m) := fun z hz =>
    hV₀t (subset_tsupport V₀ hz)
  have hV00 : ∀ z, V₀ z ≠ 0 → ∀ j, z j ≠ 0 := fun z hz => (hsupp₀ z hz).1
  have hg₀ : ∀ z ∈ regSet F N (1 / m),
      DifferentiableAt ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z := fun z hz =>
    (hz.2.differentiableAt one_ne_zero).const_mul _
  have hfd : ∀ z ∈ regSet F N (1 / m), ∀ v,
      fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z v =
        (m : ℝ) ^ 2 * fderiv ℝ (pen F N (1 / m)) z v := by
    intro z hz v
    rw [fderiv_const_mul (hz.2.differentiableAt one_ne_zero), smul_apply, smul_eq_mul]
  have hle₀ : ∀ z ∈ regSet F N (1 / m),
      fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z (V₀ z) ≤ 0 := by
    intro z hz
    rw [hfd z hz]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hV₀le z hz)
  have hh : Continuous fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1 :=
    continuous_const.mul (penW_continuous F hn (1 / m))
  -- the data of the label for its level
  have hest₂ : ∀ z ∈ cthickening δ Γ, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R₂ →
      ContDiffAt ℝ 3 (pen F (m * N) 1) (coord m N G₁ G₂ (z, ξ)) ∧
      ∀ v : ZMod N → Ambient n, ‖v‖ ≤ κ →
        fderiv ℝ (psi m N F G₁ G₂) (z, ξ) (v, swapJ ξ) ≤
          fderiv ℝ (psi m N F G₁ G₂) (z, 0) (v, 0) - c * ‖ξ‖ ^ 2 := fun z hz ξ hξ =>
    hest z hz ξ (hξ.trans hR₂R)
  have hquad₂ : ∀ z ∈ cthickening δ Γ, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R₂ →
      |psi m N F G₁ G₂ (z, ξ) - psi m N F G₁ G₂ (z, 0)| ≤ C₁ * ‖ξ‖ ^ 2 := fun z hz ξ hξ =>
    hquad z hz ξ (hξ.trans hR₂R)
  have hsmall'' : (C₁ + 1) * (B * κ'' + 2 * M / lam) ≤ min (c / (b + p + 1)) 2 / 2 := by
    have h1 : B * κ'' ≤ B * κ' := mul_le_mul_of_nonneg_left hκ''κ' hB0
    calc (C₁ + 1) * (B * κ'' + 2 * M / lam) ≤ (C₁ + 1) * (B * κ' + 2 * M / lam) := by
          gcongr
      _ ≤ _ := hsmall
  have hnzZ₁ : ∀ z ∈ closure (thickening (3 * δ / 4) Γ), ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ),
      ‖ξ‖ ≤ R₁ → ∀ j, coord m N G₁ G₂ (z, ξ) j ≠ 0 := fun z hz ξ hξ =>
    hnzK z (interior_subset (hclZ₁ hz)) ξ (hξ.trans hR₁nz)
  have hV₀le' : ∀ z ∈ cthickening δ Γ, fderiv ℝ (pen F N (1 / m)) z (V₀ z) ≤ 0 := fun z hz =>
    hV₀le z (hK₀reg hz)
  have hV₀lt' : ∀ z ∈ cthickening δ Γ, fderiv ℝ (pen F N (1 / m)) z ≠ 0 →
      fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0 := fun z hz hne =>
    hV₀lt z (hK₀reg hz) (hK₀val z hz).1.le (hK₀val z hz).2.le hne
  obtain ⟨hUo, hWs, hWle, hWlt, hTc, hTU, hβT, hβle, hβlt⟩ := label_level (F := F) (ψ := ψ)
    (V₀ := V₀) hG₁ hG₂ hK₀c hR₂ hc hC₁ hK₀u hest₂ hquad₂ hχ hχ01 hB hM hlam hr hsmall'' hκ''κ
    (hΓ.isBounded.thickening) hclZ₁ hχZ hR₁.le hR₁R₂ hrR hnzZ₁ hV₀ hV₀b hV₀le'
    hV₀lt'
  -- further facts
  have hsuppχK : tsupport χ₀ ⊆ cthickening δ Γ := fun z hz => interior_subset (hclZ₁ (hχZ hz))
  have hsuppχ : tsupport χ₀ ⊆ cthickening δ Γ ∩ {z | IsUnit (matA m N G₁ G₂ ψ z)} :=
    fun z hz => ⟨hsuppχK hz, hK₀u z (hsuppχK hz)⟩
  have hZ₀o : IsOpen (thickening (δ / 8) Γ) := isOpen_thickening
  have hZ₀'o : IsOpen (thickening (δ / 16) Γ) := isOpen_thickening
  have hregion : IsOpen (region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁) :=
    region_isOpen m N ψ hG₁ hG₂ isOpen_thickening R₁
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    positivity
  have hint : ∀ z, τ z ∈ interior (cthickening δ Γ) ↔ z ∈ interior (cthickening δ Γ) :=
    Finsler.InvariantThickening.interior_invariant τ hτ (hcth δ)
  have hTubeτ := Finsler.LabelRegionRotation.tube_half_iff m N G₁ G₂ a d₁ d₂
    hd₁ hd₂ h₁ h₂ ha (fun z hz => (hth (3 * δ / 4) z).mpr hz) (ρ := R₁)
  have hRegτ := Finsler.LabelRegionRotation.region_half_iff m N G₁ G₂ a d₁ d₂
    hd₁ hd₂ h₁ h₂ ψ ha (fun z hz => (hth (3 * δ / 4) z).mpr hz)
    (fun z hz => hK₀u z (hZ₁K hz)) (ρ := R₁)
  refine ⟨region m N G₁ G₂ ψ (interior (cthickening δ Γ)) R₂, splitW m N G₁ G₂ ψ V₀,
    beta m N F G₁ G₂ ψ χ₀ r lam, critSet m N F ψ (cthickening δ Γ) (G₁ := G₁) (G₂ := G₂),
    tube m N G₁ G₂ (thickening (3 * δ / 4) Γ) R₁,
    labelSetA m N G₁ G₂ ψ (thickening (δ / 8) Γ)
      (region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁) ρ,
    labelSetA m N G₁ G₂ ψ (thickening (δ / 16) Γ)
      (region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁) ρ',
    thickening (δ / 8) Γ, descentOf hL₀ hV00 hg₀ hsupp₀ hle₀, ?_, ?_, hTubeτ, ?_, ?_, ?_, ?_, hth (δ / 8), hUo, ?_, ?_, hWs, hWle, hWlt,
    hTc, hTU, hβT, ?_, ?_, hβle, hβlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hdisr : Disjoint {z : Om n N | z.1 ∈ thickening (δ / 8) Γ} Wrest := by
      rw [Set.disjoint_left]
      intro z hz hzW
      exact hWΓ z hzW (hK₀δ₁ (hZ₁K (hZ₀Z₁ hz)))
    have hstrictr : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ →
        z ∉ {z : Om n N | z.1 ∈ thickening (δ / 16) Γ} ∪ Wrest →
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
          (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
      intro z h1 h2 hz
      have hne : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := by
        intro h0
        rcases hrcrit z h1 h2 h0 with hΓz | hW
        · exact hz (Or.inl (self_subset_thickening (by positivity) Γ hΓz))
        · exact hz (Or.inr hW)
      have hreg := hbandreg z h1 h2
      have hlt := hV₀lt z.1 hreg h1 h2 hne
      have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
        rw [hfd z.1 hreg]
        exact mul_neg_of_pos_of_neg hm2 hlt
      exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
    have hmargin : ∀ z ∈ thickening (δ / 16) Γ, ∀ z' : ZMod N → Ambient n, ‖z' - z‖ ≤ κ'' →
        z' ∈ thickening (δ / 8) Γ := by
      intro z hz z' hz'
      exact margin_thickening (κ := κ'') (by linarith only [hκ''δ, hδ]) hz
        (by rw [dist_eq_norm]; exact hz')
    have hψstrict : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≠ c₀ →
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
          (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
      intro z h1 h2 hne
      have hne' : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := fun h0 => hne (hrval z h1 h2 h0)
      have hreg := hbandreg z h1 h2
      have hlt := hV₀lt z.1 hreg h1 h2 hne'
      have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
        rw [hfd z.1 hreg]
        exact mul_neg_of_pos_of_neg hm2 hlt
      exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
    have hregion : IsOpen (region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁) :=
      region_isOpen m N ψ hG₁ hG₂ isOpen_thickening R₁
    have hUsub : region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁ ⊆ 𝒰 := by
      rintro Q ⟨hu, hz, hx, _⟩
      have hxR : ‖xiOf m N G₁ G₂ ψ Q‖ ≤ R𝒰 := hx.le.trans (by
        rw [hR₁def]
        linarith only [hR₂𝒰, hR₂])
      have h := h𝒰tube (zOf m N Q) (hZ₁K hz) (xiOf m N G₁ G₂ ψ Q) hxR
      rw [mem_preimage, coord_inverse m N G₁ G₂ ψ hu] at h
      exact h
    let B : RootTubeData F (G₁ := G₁) (G₂ := G₂) ψ a Γ Wrest a₀ b₀ c₀ 𝒰 := {
      lower := ha₀c₀, upper := hc₀b₀, circle_value := hΓc₀,
      rest_open := hWrest, compact_band := hKr,
      V := V₀, K := K₀', lipschitz := hL₀, nonzero := hV00, diff := hg₀,
      supp := hsupp₀, nonpos := hle₀, κ := κ'', ρ := ρ, κ_pos := hκ'', ρ_pos := hρ,
      bound := hV₀b, Z := thickening (δ / 16) Γ, Z₀ := thickening (δ / 8) Γ,
      Z_open := isOpen_thickening, Z₀_open := isOpen_thickening,
      circle_mem := self_subset_thickening (by positivity) Γ,
      subset := hZ₀'Z₀, Z_invariant := hth (δ / 16), Z₀_invariant := hth (δ / 8),
      margin := hmargin, root_nonzero := fun z hz => hK₀nz z (hZ₁K (hZ₀Z₁ hz)),
      U := region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁,
      U_open := hregion, U_subset := hUsub,
      tube := label_regular m N ψ hZ₀Z₁ hρR₁ (fun z hz => hK₀u z (hZ₁K hz))
        (fun z hz ξ hξ => hnzZ₁ z (subset_closure hz) ξ hξ.le),
      disjoint := hdisr,
      fixed := Finsler.RootFlowFixed.descent_fixed hL₀ hV00 hg₀ hsupp₀ hle₀ (red m N a) hV₀τ,
      small_strict := hstrictr, value_strict := hψstrict
    }
    refine ⟨B, rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · exact region_subset_tube m N ψ
    · rintro Q ⟨hu, hz, hx, hnz⟩
      exact ⟨hu, hclZ₁ (subset_closure hz), hx.trans hR₁R₂, hnz⟩
    · intro Q
      rfl
    · rw [hρ'def]
    · have hρr : 2 * ρ ^ 2 ≤ r ^ 2 := by
        have h3 : ρ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ hρ.le hρr2 2
        nlinarith [sq_nonneg r]
      exact Finsler.LabelModelAgreement.on_label F G₁ G₂ ψ χ₀ hr.ne' hlam hχ1Z₀ hρr

  · intro Q
    exact Finsler.LabelRegionRotation.region_half_iff m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ ha
      (fun z hz => (hint z).mpr hz) (fun z hz => hK₀u z (interior_subset hz)) Q
  · intro Q hQ
    exact Finsler.RotationNatural.splitW_rotA m N G₁ G₂ ψ V₀ a d₁ d₂ hd₁ hd₂ hG₁ hG₂
      h₁ h₂ hV₀τ hQ.1 (hK₀u _ (interior_subset ((hint _).mpr hQ.2.1)))
  · intro Q
    by_cases hQ : Q ∈ tube m N G₁ G₂ (thickening (3 * δ / 4) Γ) R₁
    · have hu := hTU hQ
      exact Finsler.LabelRotation.beta_rotA m N F G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ hu.1
        (hK₀u _ (interior_subset ((hint _).mpr hu.2.1))) χ₀ hχτ r lam
    · have hQ' : rotA (m * N) a Q ∉ tube m N G₁ G₂ (thickening (3 * δ / 4) Γ) R₁ :=
        fun h => hQ ((hTubeτ Q).mp h)
      rw [image_eq_zero_of_notMem_tsupport (fun h => hQ' (hβT h)),
        image_eq_zero_of_notMem_tsupport (fun h => hQ (hβT h))]
  · intro Q
    exact Finsler.LabelSetRotation.labelSetA_half_iff m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ ha
      (fun z hz => (hth (δ / 8) z).mpr hz) (fun y hy => (hRegτ y).mpr hy)
      (fun z hz => hK₀u z (hZ₁K (hZ₀Z₁ hz))) Q
  · intro Q
    exact Finsler.LabelSetRotation.labelSetA_half_iff m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ ha
      (fun z hz => (hth (δ / 16) z).mpr hz) (fun y hy => (hRegτ y).mpr hy)
      (fun z hz => hK₀u z (hZ₁K (hZ₀Z₁ (hZ₀'Z₀ hz)))) Q
  · -- the region lies in 𝒰
    rintro Q ⟨hu, hz, hx, -⟩
    have h := h𝒰tube (zOf m N Q) (interior_subset hz) (xiOf m N G₁ G₂ ψ Q) (hx.le.trans hR₂𝒰)
    rw [mem_preimage, coord_inverse m N G₁ G₂ ψ hu] at h
    exact h
  · -- the region lies in the regular set
    rintro Q ⟨hu, hz, hx, hnz⟩
    refine ⟨hnz, ?_⟩
    have h := (hest (zOf m N Q) (interior_subset hz) (xiOf m N G₁ G₂ ψ Q) (hx.le.trans hR₂R)).1
    rw [coord_inverse m N G₁ G₂ ψ hu] at h
    exact h.of_le (by norm_num)
  · -- the deformation is differentiable
    exact beta_differentiableAt m N F G₁ G₂ ψ hG₁ hG₂ hR₂.le (fun z hz ξ hξ => (hest₂ z hz ξ hξ).1)
      hχ hsuppχ hr.ne' hlam hrR₂
  · -- the deformation is small
    intro y
    have h := abs_beta_le m N F G₁ G₂ ψ hR₂.le hquad₂ hC₁ hsuppχK (fun z => (hχ01 z).1)
      (fun z => (hχ01 z).2) hr.ne' hlam hrR₂ y
    have hRη1 : Rη ≤ 1 := min_le_left _ _
    have hRη2 : Rη ≤ η / (C₁ + 1) := min_le_right _ _
    have h3 : r ^ 2 * Real.exp lam ≤ Rη := by
      have h4 : R₂ ^ 2 ≤ Rη ^ 2 := pow_le_pow_left₀ hR₂.le hR₂η 2
      have h5 : Rη ^ 2 ≤ Rη := by
        rw [sq]
        exact mul_le_of_le_one_left hRη.le hRη1
      linarith only [hrR₂, h4, h5]
    have h6 : (C₁ + 1) * (r ^ 2 * Real.exp lam) ≤ η := by
      have h7 : (C₁ + 1) * (r ^ 2 * Real.exp lam) ≤ (C₁ + 1) * (η / (C₁ + 1)) :=
        mul_le_mul_of_nonneg_left (h3.trans hRη2) hC₁1.le
      rwa [mul_div_cancel₀ η hC₁1.ne'] at h7
    exact h.trans h6
  · exact Finsler.AmbientTrap.labelSetA_isOpen m N G₁ G₂ ψ hG₁ hG₂ hZ₀o hregion
  · exact Finsler.AmbientTrap.labelSetA_isOpen m N G₁ G₂ ψ hG₁ hG₂ hZ₀'o hregion
  · rintro Q ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, hZ₀'Z₀ h2, lt_of_lt_of_le h3 hρ'ρ, lt_of_lt_of_le h4 hρ'ρ, h5⟩
  · rintro Q ⟨-, -, -, -, h5⟩
    exact region_subset_tube m N ψ h5
  · -- the critical set lies in the small label set
    intro Q hQ
    obtain ⟨hu, hzK, hcrit, hxi⟩ := hQ
    have hzΓ := hiso _ (hK₀𝒪 _ hzK) hcrit
    refine ⟨hu, self_subset_thickening (by positivity) Γ hzΓ, ?_, ?_,
      ⟨hu, self_subset_thickening (by positivity) Γ hzΓ, ?_, Q.2⟩⟩
    · rw [hxi, map_zero, norm_zero]
      exact hρ'0
    · rw [hxi, map_zero, norm_zero]
      exact hρ'0
    · rw [hxi, norm_zero]
      exact hR₁
  · -- the iterated root circle lies in the tube
    intro z hz
    refine ⟨(z, 0), ⟨subset_closure (self_subset_thickening (by positivity) Γ hz),
      mem_closedBall_self hR₁.le⟩, ?_⟩
    exact coord_zero m N G₁ G₂ z
  · -- the values on the critical set
    intro y hy
    obtain ⟨hu, hzK, hcrit, hxi⟩ := hy
    have hzΓ := hiso _ (hK₀𝒪 _ hzK) hcrit
    have hy0 : y = coord m N G₁ G₂ (zOf m N y, 0) := by
      have h := coord_inverse m N G₁ G₂ ψ hu
      rw [hxi] at h
      exact h.symm
    refine ⟨?_, ?_⟩
    · have h1 : psi m N F G₁ G₂ (zOf m N y, 0) = (m : ℝ) ^ 2 * pen F N (1 / m) (zOf m N y) :=
        psi_zero m N F G₁ G₂ _
      have h2 : psi m N F G₁ G₂ (zOf m N y, 0) = pen F (m * N) 1 y := by
        change pen F (m * N) 1 (coord m N G₁ G₂ (zOf m N y, 0)) = _
        rw [← hy0]
      rw [← h2, h1]
      exact hΓc₀ _ hzΓ
    · have hc : cOf m N G₁ G₂ ψ y = (zOf m N y, 0) := Prod.ext rfl hxi
      unfold beta
      rw [hc]
      have hm : model m N F G₁ G₂ (zOf m N y, 0) = psi m N F G₁ G₂ (zOf m N y, 0) := by
        simp [model, sqX, sqY]
      rw [hm, sub_self, mul_zero]
  · -- the root label set is open
    exact hZ₀o.preimage continuous_subtype_val
  · -- the root label set avoids the rest
    rw [Set.disjoint_left]
    intro z hz hzW
    exact hWΓ z hzW (hK₀δ₁ (hZ₁K (hZ₀Z₁ hz)))
  · -- the root descent decreases strictly off the root label set and the rest
    intro z h1 h2 hz
    have hne : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := by
      intro h0
      rcases hrcrit z h1 h2 h0 with hΓz | hW
      · exact hz (Or.inl (self_subset_thickening (by positivity) Γ hΓz))
      · exact hz (Or.inr hW)
    have hreg := hbandreg z h1 h2
    have hlt := hV₀lt z.1 hreg h1 h2 hne
    have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
      rw [hfd z.1 hreg]
      exact mul_neg_of_pos_of_neg hm2 hlt
    exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
  · -- the root descent decreases strictly off the critical value
    intro z h1 h2 hne
    have hne' : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := fun h0 => hne (hrval z h1 h2 h0)
    have hreg := hbandreg z h1 h2
    have hlt := hV₀lt z.1 hreg h1 h2 hne'
    have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
      rw [hfd z.1 hreg]
      exact mul_neg_of_pos_of_neg hm2 hlt
    exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
  · -- the shift of the label
    intro V KL hL hV0 g O hg hsupp hle hVT hgT a₀a b₀a ha₀a hb₀a hgc hKb R hR hdis hstrict
    have hVT' : ∀ y ∈ region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁,
        V y = splitW m N G₁ G₂ ψ V₀ y := fun y hy => hVT y (region_subset_tube m N ψ hy)
    have hgT' : ∀ y ∈ region m N G₁ G₂ ψ (thickening (3 * δ / 4) Γ) R₁,
        g y = gDef m N F G₁ G₂ ψ χ₀ r lam y := fun y hy => hgT y (region_subset_tube m N ψ hy)
    have hdisr : Disjoint {z : Om n N | z.1 ∈ thickening (δ / 8) Γ} Wrest := by
      rw [Set.disjoint_left]
      intro z hz hzW
      exact hWΓ z hzW (hK₀δ₁ (hZ₁K (hZ₀Z₁ hz)))
    have hstrictr : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ →
        z ∉ {z : Om n N | z.1 ∈ thickening (δ / 16) Γ} ∪ Wrest →
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
          (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
      intro z h1 h2 hz
      have hne : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := by
        intro h0
        rcases hrcrit z h1 h2 h0 with hΓz | hW
        · exact hz (Or.inl (self_subset_thickening (by positivity) Γ hΓz))
        · exact hz (Or.inr hW)
      have hreg := hbandreg z h1 h2
      have hlt := hV₀lt z.1 hreg h1 h2 hne
      have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
        rw [hfd z.1 hreg]
        exact mul_neg_of_pos_of_neg hm2 hlt
      exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
    have hmargin : ∀ z ∈ thickening (δ / 16) Γ, ∀ z' : ZMod N → Ambient n, ‖z' - z‖ ≤ κ'' →
        z' ∈ thickening (δ / 8) Γ := by
      intro z hz z' hz'
      exact margin_thickening (κ := κ'') (by linarith only [hκ''δ, hδ]) hz
        (by rw [dist_eq_norm]; exact hz')
    have hρr : 2 * ρ ^ 2 ≤ r ^ 2 := by
      have h2 : ρ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ hρ.le hρr2 2
      have h3 : (r / 2) ^ 2 = r ^ 2 / 4 := by ring
      have h4 : 0 ≤ r ^ 2 := sq_nonneg r
      linarith only [h2, h3, h4]
    obtain ⟨d, hd, hfull⟩ := Finsler.LabelFull.label_full m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle
      hL₀ hV00 hg₀ hsupp₀ hle₀ hh hG₁ hG₂ (χ₀ := χ₀) hlam hr isOpen_thickening
      (fun z hz => hK₀u z (hZ₁K hz)) (fun z hz ξ hξ => hnzZ₁ z (subset_closure hz) ξ hξ.le)
      hZ₀o hZ₀'o hZ₀Z₁ hZ₀'Z₀ (fun z hz => hK₀nz z (hZ₁K (hZ₀Z₁ hz))) hχ1Z₀ hρ
      hρR₁ hρr hρ'e hV₀b hmargin hVT' hgT' hgc hKb hR hdis hstrict hKr hWrest hdisr
      hstrictr
    -- the root descent decreases strictly at the band polygons off the critical value
    have hψstrict : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≠ c₀ →
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
          (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
      intro z h1 h2 hne
      have hne' : fderiv ℝ (pen F N (1 / m)) z.1 ≠ 0 := fun h0 => hne (hrval z h1 h2 h0)
      have hreg := hbandreg z h1 h2
      have hlt := hV₀lt z.1 hreg h1 h2 hne'
      have hneg' : fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z.1 (V₀ z.1) < 0 := by
        rw [hfd z.1 hreg]
        exact mul_neg_of_pos_of_neg hm2 hlt
      exact descentOf_lt hL₀ hV00 hg₀ hsupp₀ hle₀ z hneg'
    set d' : ℝ := min (d / 2) (min (ρ ^ 2 / 4) (min ((c₀ - a₀) / 2) (min ((b₀ - c₀) / 2)
      (min (c₀ - a₀a) (b₀a - c₀))))) with hd'def
    have hd'0 : 0 < d' := by
      refine lt_min (half_pos hd) (lt_min (by positivity) (lt_min (by linarith only [ha₀c₀])
        (lt_min (by linarith only [hc₀b₀]) (lt_min (by linarith only [ha₀a]) (by linarith only [hb₀a])))))
    have hd'1 : d' ≤ d / 2 := min_le_left _ _
    have hd'2 : d' ≤ ρ ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
    have hd'3 : d' ≤ (c₀ - a₀) / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hd'4 : d' ≤ (b₀ - c₀) / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hd'5 : d' ≤ c₀ - a₀a := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hd'6 : d' ≤ b₀a - c₀ := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    refine ⟨d', hd'0, fun a c T hT ha hc hcd => ?_⟩
    have hac : a ≤ c := by linarith only [ha, hc]
    have hca : 0 ≤ c - a := by linarith only [ha, hc]
    -- the widening of the cuts is at most (c - a) / 2
    have hE : 2 ≤ Real.exp (2 * T) - 1 := by
      have h1 : Real.exp 1 ≥ 2 := by
        have := Real.add_one_le_exp 1
        linarith only [this]
      have h2 : Real.exp (2 * T) ≥ Real.exp 2 := Real.exp_le_exp.mpr (by linarith only [hT])
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith only [h1, h2, h3]
    have hε0 : 0 ≤ (c - a) / (Real.exp (2 * T) - 1) := div_nonneg hca (by linarith only [hE])
    have hε : (c - a) / (Real.exp (2 * T) - 1) ≤ (c - a) / 2 :=
      div_le_div_of_nonneg_left hca two_pos hE
    have h1 : 2 * (c - a) < d := by linarith only [hcd, hd'1]
    have h2 : 4 * (c - a) < ρ ^ 2 := by linarith only [hcd, hd'2]
    have h3 : a₀a ≤ a := by linarith only [hcd, hd'5, hc]
    have h4 : c ≤ b₀a := by linarith only [hcd, hd'6, ha]
    have h5 : a₀ ≤ a - (c - a) / (Real.exp (2 * T) - 1) := by
      linarith only [hcd, hd'3, hc, hε, ha₀c₀]
    have h6 : c + (c - a) / (Real.exp (2 * T) - 1) ≤ b₀ := by
      linarith only [hcd, hd'4, ha, hε, hc₀b₀]
    have hstrip : ∀ z : Om n N, c ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ c + (c - a) / (Real.exp (2 * T) - 1) →
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
          (m : ℝ) ^ 2 * pen F N (1 / m) z.1 := by
      intro z hz1 hz2
      refine hψstrict z (by linarith only [hz1, h5, hε0, hac]) (by linarith only [hz2, h6]) ?_
      intro heq
      linarith only [heq, hz1, hc]
    exact hfull a c T hT hac h2 h1 h3 h4 h5 h6 hstrip


end

end Finsler.LabelPackRoot
