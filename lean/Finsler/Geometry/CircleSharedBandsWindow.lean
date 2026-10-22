module

public import Finsler.Geometry.LabelPackBandsReidx
public import Finsler.Geometry.CircleFixedWindow
public import Finsler.Geometry.CircleLabelFields
public import Finsler.Geometry.LabelPackFixed
public import Finsler.Geometry.LabelRootSupport
public import Finsler.Geometry.FixedLabelTrapped

/-! Actual signed frames and shared label data give finite fixed support centered at the
half-iterate index I(j), under explicit root support and ambient band hypotheses. -/

@[expose] public section

namespace Finsler.CircleSharedBandsWindow

open Finsler.GeodesicFrames Finsler.CircleHalfRotation
open Module Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientPenalty
open Finsler.AmbientSymmetry Finsler.PolygonIterate Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.CircleFrameField Finsler.FrameCoordinates
open Finsler.FrameInverse Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform
open Finsler.LensContinuation Finsler.LabelTransport Finsler.AmbientDescent Finsler.FlowLens Finsler.LensFamily
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LabelRootData Finsler.LabelPackRoot Finsler.LabelPackRootReidx Finsler.LabelPack
open scoped NNReal ContDiff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_centered_support {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (γ : Finsler.Geodesics.ClosedGeodesic F) (m s j : ℕ) [NeZero m] [NeZero s] [NeZero j]
    (hms : m * s = 2 * j) (A : ℕ) (hI : (iterData γ).I s ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K],
      ∀ (hK : m * (s * (2 * N)) = K) (b p : ℕ)
        (S₁ : SignedFrameField γ s m N 1 b) (S₂ : SignedFrameField γ s m N (-1) p),
    ∀ (ψ : normal (rotL (n := n) m (s * (2 * N))) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (Γ : Set (ZMod (s * (2 * N)) → Ambient n)) (R : Set (Om n (s * (2 * N))))
  (a₀ b₀ c₀ : ℝ) (𝒰 : Set (ZMod K → Ambient n))
  (U : Set (ZMod K → Ambient n))
  (W : (ZMod K → Ambient n) → ZMod K → Ambient n)
  (β : (ZMod K → Ambient n) → ℝ) (T₀ : Set (ZMod K → Ambient n))
  (𝒲 𝒲' : Set (Om n K)) (Z₀ : Set (ZMod (s * (2 * N)) → Ambient n))
  (ψ₀ : Descent (Om n (s * (2 * N))) (fun z : Om n (s * (2 * N)) => (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1))
  (hshare : SharedRootAt F (G₁ := S₁.G) (G₂ := S₂.G) hK ψ (halfIndex m s N) Γ R a₀ b₀ c₀ 𝒰 U W β T₀ 𝒲 𝒲' Z₀ ψ₀)
  (hab₀ : a₀ ≤ b₀),
    ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
    (hL : LipschitzWith KL V) (hV0 : ∀ Q, V Q ≠ 0 → ∀ j, Q j ≠ 0)
    {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
    (hg : ∀ Q ∈ O, DifferentiableAt ℝ g Q) (hsupp : ∀ Q, V Q ≠ 0 → Q ∈ O)
    (hle : ∀ Q ∈ O, fderiv ℝ g Q (V Q) ≤ 0)
    (hVT : ∀ Q ∈ T₀, V Q = W Q)
    (hgT : ∀ Q ∈ T₀, g Q = pen F K 1 Q + β Q)
    {a₀a b₀a : ℝ} (ha₀a : a₀a < c₀) (hb₀a : c₀ < b₀a)
    {Ra : Set (Om n K)} (hRa : IsOpen Ra)
    (hAdis : Disjoint (𝒲) Ra)
    (hgc : Continuous fun Q : Om n K => g Q.1)
    (hKa : IsCompact {Q : Om n K | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a})
    (hstricta : ∀ Q : Om n K, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a →
      Q ∉ 𝒲' ∪ Ra →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH
      (fun z : TopCat.of {z : Om n (s * (2 * N)) | rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1) hab₀ q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH
      (fun z : TopCat.of {z : Om n (s * (2 * N)) | rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1) hab₀ q, z = 0),
    ∃ d : ℝ, 0 < d ∧ ∀ l u T : ℝ, 1 ≤ T → l < c₀ → c₀ < u →
      a₀ ≤ l - (u - l) / (Real.exp (2 * T) - 1) →
      u + (u - l) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (u + (u - l) / (Real.exp (2 * T) - 1)) - (l - (u - l) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (inter_subset_inter_left
          {Q : Om n K | rotA K (reidxShift hK (halfIndex m s N)) Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n K => g Q.1)
            (descentOf hL hV0 hg hsupp hle) (𝒲) l u T)))) q)) ∧
        ∀ q : ℕ, (A : ℝ) < |(q : ℝ) - (iterData γ).I j| → ∀ z :
          H (triv (pairOf (inter_subset_inter_left
            {Q : Om n K | rotA K (reidxShift hK (halfIndex m s N)) Q.1 = Q.1}
            (partY_sub_partU (fun Q : Om n K => g Q.1)
              (descentOf hL hV0 hg hsupp hle) (𝒲) l u T)))) q, z = 0 := by
  obtain ⟨N₀, hN₀⟩ := Finsler.CircleFixedWindow.exists_window γ m s j hms A hI
  refine ⟨N₀, fun N hN _ K _ hK b p S₁ S₂ ψ Γ R a₀ b₀ c₀ 𝒰 U W β T₀ 𝒲 𝒲' Z₀ ψ₀ hshare hab₀
    V KL hL hV0 g O hg hsupp hle hVT hgT a₀a b₀a ha₀a hb₀a Ra hRa hAdis hgc hKa hstricta hf hz => ?_⟩
  obtain ⟨d, hd, hs⟩ := Finsler.LabelPackBandsReidx.exists_fixed_support hK F hn S₁.G S₂.G ψ
    (halfIndex m s N) Γ R a₀ b₀ c₀ 𝒰 U W β T₀ 𝒲 𝒲' Z₀ ψ₀ hshare hab₀
    S₁.smooth S₂.smooth S₁.d S₂.d S₁.signs S₂.signs
    (Finsler.CircleLabelFields.field_equivariant S₁) (Finsler.CircleLabelFields.field_equivariant S₂)
    hL hV0 hg hsupp hle hVT hgT ha₀a hb₀a hRa hAdis hgc hKa hstricta A hf hz
  refine ⟨d, hd, fun l u T hT hl hu hlo hhi hw => ?_⟩
  obtain ⟨hfq, hzq⟩ := hs l u T hT hl hu hlo hhi hw
  exact ⟨hfq, fun q hq => hzq q (hN₀ N hN S₁ S₂ ψ A q le_rfl hq)⟩

end

end Finsler.CircleSharedBandsWindow

