module

public import Finsler.Topology.CircleLabel
public import Finsler.Topology.ReversalLabelData

/-! package the full ordinary label estimates so reversal can
transport the same root data without identifying independently chosen iteration periods. -/

@[expose] public section

namespace Finsler.LocalLabelPacket

open Set Module Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.PolygonDescent Finsler.PolygonSampling Finsler.RootIsolation
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.CircleRoot Finsler.CircleLabel Finsler.GeodesicFrames
open Finsler.LevelField Finsler.AmbientPenalty Finsler.AmbientDescent
open Finsler.FlowLens Finsler.LensContinuation Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.AmbientLoopPairs Finsler.AmbientSymmetry
open Finsler.PolygonDescentK Finsler.RevLabel Finsler.AmbientK Finsler.ReversalLabelData
open scoped ContDiff NNReal
noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5

structure Packet (n K : ℕ) where
  b : ℕ
  r : ℝ → ℝ → ℝ → ℕ → ℕ
  U : Set (ZMod K → Ambient n)
  W : (ZMod K → Ambient n) → ZMod K → Ambient n
  β : (ZMod K → Ambient n) → ℝ
  C : Set (ZMod K → Ambient n)
  T : Set (ZMod K → Ambient n)
  big : Set (Om n K)
  small : Set (Om n K)

variable {n K : ℕ} [NeZero K]

def Analytic (F : ReversibleMetric n) (c η : ℝ) (Γ : Set (ZMod K → Ambient n))
    (d : Packet n K) : Prop :=
  IsOpen d.U ∧ d.U ⊆ regSet F K 1 ∧ ContDiffOn ℝ ∞ d.W d.U ∧
  (∀ y ∈ d.U, fderiv ℝ (pen F K 1) y (d.W y) ≤ 0) ∧
  (∀ y ∈ d.U, y ∉ d.C → fderiv ℝ (pen F K 1) y (d.W y) < 0) ∧
  IsCompact d.T ∧ d.T ⊆ d.U ∧ tsupport d.β ⊆ d.T ∧
  (∀ y, DifferentiableAt ℝ d.β y) ∧ (∀ y, |d.β y| ≤ η) ∧
  (∀ y ∈ tsupport d.β, fderiv ℝ (fun y => pen F K 1 y + d.β y) y (d.W y) ≤ 0) ∧
  (∀ y ∈ tsupport d.β, y ∉ d.C →
    fderiv ℝ (fun y => pen F K 1 y + d.β y) y (d.W y) < 0) ∧
  IsOpen d.big ∧ IsOpen d.small ∧ d.small ⊆ d.big ∧
  (∀ Q ∈ d.big, Q.1 ∈ d.T) ∧ (∀ Q : Om n K, Q.1 ∈ d.C → Q ∈ d.small) ∧
  d.C ⊆ d.U ∧ Γ ⊆ d.T ∧ (∀ y ∈ d.C, pen F K 1 y = c ^ 2 ∧ d.β y = 0)

def HalfInvariant (a : ZMod K) (d : Packet n K) : Prop :=
  (∀ y, rotA K a y ∈ d.U ↔ y ∈ d.U) ∧
  (∀ y, rotA K a y ∈ d.T ↔ y ∈ d.T) ∧
  (∀ y ∈ d.U, d.W (rotA K a y) = rotA K a (d.W y)) ∧
  (∀ y, d.β (rotA K a y) = d.β y) ∧
  (∀ Q, (⟨rotA K a Q.1, rotA_ne_zero K a Q.2⟩ : Om n K) ∈ d.big ↔ Q ∈ d.big) ∧
  (∀ Q, (⟨rotA K a Q.1, rotA_ne_zero K a Q.2⟩ : Om n K) ∈ d.small ↔ Q ∈ d.small)

def RootBound (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (c x : ℝ) (d : Packet n K) : Prop :=
  ∃ dr : ℝ, 0 < dr ∧ ∀ a c' t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < c' → c' - a < dr →
    ∀ j : ℕ, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin x)))) j) →
      d.r a c' t j ≤ finrank (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin x)))) j)

def Model (F : ReversibleMetric n) (c : ℝ) (d : Packet n K) : Prop :=
  ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
    (hL : LipschitzWith KL V) (hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
    {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
    (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
    (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0),
    (∀ y ∈ d.T, V y = d.W y) → (∀ y ∈ d.T, g y = pen F K 1 y + d.β y) →
    ∀ {a₀ b₀ : ℝ}, a₀ < c ^ 2 → c ^ 2 < b₀ → Continuous (fun Q : Om n K => g Q.1) →
    IsCompact {Q : Om n K | a₀ ≤ g Q.1 ∧ g Q.1 ≤ b₀} →
    ∀ {R : Set (Om n K)}, IsOpen R → Disjoint d.big R →
    (∀ Q : Om n K, a₀ ≤ g Q.1 → g Q.1 ≤ b₀ → Q ∉ d.small ∪ R →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
    ∃ e : ℝ, 0 < e ∧ ∀ a b t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < b → b - a < e →
      (∀ j : ℕ, finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
        (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) d.big a b t))) (j + d.b)) =
          d.r a b t j) ∧
      (∀ j : ℕ, j < d.b → ∀ x : H (triv (pairOf (partY_sub_partU
        (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) d.big a b t))) j, x = 0)

def CircleSpec (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k N : ℕ) (c η : ℝ)
    (d : Packet n K) : Prop :=
  Analytic F c η (sampleSet K (circle F c ℓ)) d ∧ HalfInvariant (k * N : ZMod K) d ∧
  d.b = (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k -
    (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I
      (Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L)) ∧
  RootBound F hfin c ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
    Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)) d ∧
  Model F c d

theorem exists_circle_packet (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    {ℓ : Set (Sphere n) × Bool} (hℓ : ℓ ∈ labels F hfin) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K' : ℕ} [NeZero K'], k * (2 * N) = K' →
      ∀ {𝒰 : Set (ZMod K' → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ circle F c ℓ, amb (samplePoly K' u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
        ∃ d : Packet n K', d.U ⊆ 𝒰 ∧ CircleSpec F hfin ℓ hℓ k N c η d := by
  obtain ⟨N₀, hN₀⟩ := circle_label_half F hn hfin hc hℓ hkc
  refine ⟨N₀, fun N hN _ K' _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
  obtain ⟨b, r, U, W, β, C, T, big, small, hUi, hTi, hWi, hβi, hbi, hsi,
    hb, hU, hU𝒰, hUr, hW, hWle, hWlt, hT, hTU, hβT, hβd, hβb, hβle, hβlt,
    hbig, hsmall, hsb, hbT, hCs, hCU, hΓT, hC, hroot, hmodel⟩ := hN₀ N hN hK h𝒰 hΓ hη
  refine ⟨⟨b, r, U, W, β, C, T, big, small⟩, hU𝒰,
    ⟨hU, hUr, hW, hWle, hWlt, hT, hTU, hβT, hβd, hβb, hβle, hβlt,
      hbig, hsmall, hsb, hbT, hCs, hCU, ?_, hC⟩,
    ⟨hUi, hTi, hWi, hβi, hbi, hsi⟩, hb, hroot, hmodel⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hΓT u hu

end

end Finsler.LocalLabelPacket
