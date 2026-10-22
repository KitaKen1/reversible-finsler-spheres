module

public import Finsler.Topology.RootLabelPacket
public import Finsler.Topology.RootCatalogueSupport
public import Finsler.Geometry.CircleSharedBandsWindow
public import Finsler.Analysis.WidenedCuts

/-! Apply the uniform root catalogue to the retained actual circle witnesses.
Only the actual ambient band and tube agreement remain as local descent hypotheses. -/

@[expose] public section

namespace Finsler.CircleRootWindow

open Set Module Finsler.Geometry Finsler.SphereGeometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.RootLabelPacket Finsler.CircleLabelRoot
open Finsler.CircleLabel Finsler.RootCatalogue Finsler.CriticalLevels
open Finsler.CriticalCircles Finsler.GeodesicFrames Finsler.AmbientPenalty
open Finsler.OrientedCritical Finsler.LensContinuation Finsler.CircleRoot
open Finsler.AmbientSymmetry Finsler.AmbientDescent Finsler.FlowLens Finsler.LensFamily
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LabelPack Finsler.CircleHalfRotation
open scoped NNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n K : ℕ} [NeZero K]

def Window (F : ReversibleMetric n) (a : ZMod K) (A I : ℕ) (c : ℝ)
    (d : Packet n K) : Prop :=
  ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
    (hL : LipschitzWith KL V) (hV0 : ∀ Q, V Q ≠ 0 → ∀ j, Q j ≠ 0)
    {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
    (hg : ∀ Q ∈ O, DifferentiableAt ℝ g Q) (hsupp : ∀ Q, V Q ≠ 0 → Q ∈ O)
    (hle : ∀ Q ∈ O, fderiv ℝ g Q (V Q) ≤ 0),
    (∀ Q ∈ d.T, V Q = d.W Q) → (∀ Q ∈ d.T, g Q = pen F K 1 Q + d.β Q) →
    ∀ {a₀ b₀ : ℝ}, a₀ < c ^ 2 → c ^ 2 < b₀ →
    ∀ {R : Set (Om n K)}, IsOpen R → Disjoint d.big R →
    Continuous (fun Q : Om n K => g Q.1) →
    IsCompact {Q : Om n K | a₀ ≤ g Q.1 ∧ g Q.1 ≤ b₀} →
    (∀ Q : Om n K, a₀ ≤ g Q.1 → g Q.1 ≤ b₀ → Q ∉ d.small ∪ R →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
    ∃ e : ℝ, 0 < e ∧ ∀ l u T : ℝ, 1 ≤ T → l < c ^ 2 → c ^ 2 < u → u - l < e →
      (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf
        (inter_subset_inter_left {Q : Om n K | rotA K a Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n K => g Q.1)
            (descentOf hL hV0 hg hsupp hle) d.big l u T)))) q)) ∧
      ∀ q : ℕ, (A : ℝ) < |(q : ℝ) - I| → ∀ z : H (triv (pairOf
        (inter_subset_inter_left {Q : Om n K | rotA K a Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n K => g Q.1)
            (descentOf hL hV0 hg hsupp hle) d.big l u T)))) q, z = 0

theorem exists_uniform_window (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, RootCatalogue.Bounds F hfin A ∧
      ∀ ℓ (hℓ : ℓ ∈ labels F hfin) (k j : ℕ), 0 < k → ∀ [NeZero j], k = 2 * j →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K]
        {c : ℝ} {𝒰 : Set (ZMod K → Ambient n)} {d : Packet n K},
        Shared F hfin ℓ hℓ k N K c 𝒰 d →
        Window F (k * N : ZMod K) A
          ((iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I j) c d := by
  obtain ⟨A, NR, hA, _, hroot⟩ := Finsler.RootCatalogueSupport.exists_uniform_support F hfin hn
  refine ⟨A, hA, fun ℓ hℓ k j hk _ hkj => ?_⟩
  let γ := labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ)
  let s := rootOrder F hfin ℓ hℓ k
  let m := k / s
  obtain ⟨hs0, hsm, _, _⟩ := root_facts (L := (iterData γ).L) hk
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
    change s * m = k at hsm
    rw [h, mul_zero] at hsm
    omega
  have : NeZero s := ⟨hs0.ne'⟩
  have : NeZero m := ⟨hm0.ne'⟩
  have hms : m * s = 2 * j := by
    rw [Nat.mul_comm]
    exact hsm.trans hkj
  obtain ⟨NC, hNC⟩ := Finsler.CircleSharedBandsWindow.exists_centered_support F hn γ m s j hms A
    (hA ℓ hℓ k hk).1
  refine ⟨max NR NC, fun N hN _ K _ c 𝒰 d hshare => ?_⟩
  rcases hshare with ⟨s', m', hs', hm', b, p, S₁, S₂, hK, ψ, Γ, R, Z₀, ψ₀,
    hse, hme, hsm', _, _, hshared⟩
  subst s'
  subst m'
  let a₀ := (m : ℝ) ^ 2 * (isoBand F hfin (rootLevel F hfin ℓ hℓ k)).1 ^ 2
  let b₀ := (m : ℝ) ^ 2 * (isoBand F hfin (rootLevel F hfin ℓ hℓ k)).2 ^ 2
  have hab : a₀ ≤ b₀ := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (isoBand_spec F hfin (rootLevel_pos F hfin ℓ hℓ hk)).1.le
      (isoBand_le F hfin (rootLevel F hfin ℓ hℓ k)) 2) (sq_nonneg (m : ℝ))
  have hshift : reidxShift hK (halfIndex m s N) = (k * N : ZMod K) := by
    have hnum : m * s * N = k * N := by rw [Nat.mul_comm m s, hsm]
    unfold reidxShift halfIndex
    rw [hnum]
    have hcast : ∀ (B C : ℕ) (h : B = C) (i : ℕ),
        cast (congrArg ZMod h) (i : ZMod B) = (i : ZMod C) := by
      intro B C h i
      cases h
      rfl
    simpa only [Nat.cast_mul] using hcast _ K hK (k * N)
  intro V KL hL hV0 g O hg hsupp hle hVT hgT a₀a b₀a ha₀a hb₀a Ra hRa hdis hgc hKa hstrict
  obtain ⟨hf, hz⟩ := hroot ℓ hℓ k hk s rfl N ((le_max_left _ _).trans hN) m
  obtain ⟨δ, hδ, hwin⟩ := hNC N ((le_max_right _ _).trans hN)
    hK b p S₁ S₂ ψ Γ R a₀ b₀ (c ^ 2) 𝒰 d.U d.W d.β d.T d.big d.small Z₀ ψ₀ hshared hab
    hL hV0 hg hsupp hle hVT hgT ha₀a hb₀a hRa hdis hgc hKa hstrict hf hz
  have hbounds : a₀ < c ^ 2 ∧ c ^ 2 < b₀ := by
    clear hwin
    subst K
    rcases hshared with ⟨B, _⟩
    exact ⟨B.lower, B.upper⟩
  obtain ⟨e, he, hwidth⟩ := Finsler.WidenedCuts.exists_width hbounds.1 hbounds.2 hδ
  refine ⟨e, he, fun l u T hT hl hu hw => ?_⟩
  obtain ⟨hlo, hhi, hwide⟩ := hwidth l u T hT hl hu hw
  have hs := hwin l u T hT hl hu hlo hhi hwide
  rw [hshift] at hs
  exact hs

end

end Finsler.CircleRootWindow
