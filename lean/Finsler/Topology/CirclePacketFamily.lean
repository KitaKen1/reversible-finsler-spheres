module

public import Finsler.Topology.FiniteCirclePackets
public import Finsler.Geometry.LevelDescentK

/-! apply the actual K descent construction to paired complete
critical-circle packets. Critical-band coverage and disjoint ambient neighbourhoods are
explicit geometric inputs. -/

@[expose] public section

namespace Finsler.CirclePacketFamily

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.LocalLabelReverse Finsler.FiniteCirclePackets
open Finsler.CriticalCircles Finsler.PolygonDescent Finsler.PolygonLoop Finsler.PolygonCritical
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.LevelField Finsler.LevelDescentK
open Finsler.AmbientSymmetry Finsler.PolygonDescentK Finsler.AmbientK Finsler.RevLabel
open Finsler.RootIsolation Finsler.FlowLens
open scoped ContDiff NNReal
noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1200000

variable {n : ℕ} (M : ℕ) [NeZero M] {ι : Type*}

def packetFamily (d : ι → Packet n (2 * M)) (p : ι × Bool) : Packet n (2 * M) :=
  cond p.2 (d p.1) (reversePacket M (d p.1))

theorem family_analytic (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F) (k N : ι → ℕ)
    {c η : ℝ} {d : ι → Packet n (2 * M)}
    (hd : ∀ i, Spec F hfin (s i) (hs i) (k i) (N i) c η (d i)) (p : ι × Bool) :
    Analytic F c η (sampleSet (2 * M) (circle F c (s p.1, p.2))) (packetFamily M d p) := by
  rcases p with ⟨i, o⟩
  cases o
  · exact (hd i).2.1
  · exact (hd i).1.1

theorem family_half (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F) (k N : ι → ℕ)
    {c η : ℝ} {d : ι → Packet n (2 * M)}
    (hd : ∀ i, Spec F hfin (s i) (hs i) (k i) (N i) c η (d i))
    (hkn : ∀ i, k i * N i = M) (p : ι × Bool) :
    HalfInvariant (M : ZMod (2 * M)) (packetFamily M d p) := by
  rcases p with ⟨i, o⟩
  cases o
  · exact (hd i).2.2.1
  · have h := (hd i).1.2.1
    have he : (k i * N i : ZMod (2 * M)) = (M : ZMod (2 * M)) := by
      rw [← Nat.cast_mul, hkn i]
    rwa [he] at h

theorem family_model (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F) (k N : ι → ℕ)
    {c η : ℝ} {d : ι → Packet n (2 * M)}
    (hd : ∀ i, Spec F hfin (s i) (hs i) (k i) (N i) c η (d i)) (p : ι × Bool) :
    Model F c (packetFamily M d p) := by
  rcases p with ⟨i, o⟩
  cases o
  · exact (hd i).2.2.2
  · exact (hd i).1.2.2.2.2

theorem family_disjoint {d : ι → Packet n (2 * M)}
    {U : ι → Set (ZMod (2 * M) → Ambient n)} (hsub : ∀ i, (d i).U ⊆ U i)
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUr : ∀ i j, Disjoint (U i) (revA (2 * M) ⁻¹' U j))
    (p q : ι × Bool) (hpq : p ≠ q) :
    Disjoint (packetFamily M d p).U (packetFamily M d q).U := by
  have he : (fun p => (packetFamily M d p).U) =
      Finsler.ReversalFamily.setFamily (revA (2 * M)) (fun i => (d i).U) := by
    funext ⟨i, o⟩
    cases o <;> rfl
  change Disjoint ((fun p => (packetFamily M d p).U) p) ((fun p => (packetFamily M d p).U) q)
  rw [he]
  exact Finsler.ReversalFamily.sets_disjoint (revA (2 * M))
    (fun i j hij => (hU i j hij).mono (hsub i) (hsub j))
    (fun i j => (hUr i j).mono (hsub i) (preimage_mono (hsub j))) p q hpq

variable [Fintype ι]

def deformed (F : ReversibleMetric n) (p : ι → Packet n (2 * M))
    (y : ZMod (2 * M) → Ambient n) : ℝ := pen F (2 * M) 1 y + ∑ i, (p i).β y

structure Global (F : ReversibleMetric n) (p : ι → Packet n (2 * M)) (a₀ b₀ : ℝ) where
  V : (ZMod (2 * M) → Ambient n) → ZMod (2 * M) → Ambient n
  KL : ℝ≥0
  lipschitz : LipschitzWith KL V
  nonzero : ∀ P : ZMod (2 * M) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0
  differentiable : ∀ P ∈ regSet F (2 * M) 1, DifferentiableAt ℝ (deformed M F p) P
  supported : ∀ P, V P ≠ 0 → P ∈ regSet F (2 * M) 1
  nonpos : ∀ P ∈ regSet F (2 * M) 1, fderiv ℝ (deformed M F p) P (V P) ≤ 0
  agrees : ∀ i y, y ∈ (p i).T → V y = (p i).W y
  rho : ∀ t Q, (descentOf lipschitz nonzero differentiable supported nonpos).flow t ((ambK M).ρ Q) =
    (ambK M).ρ ((descentOf lipschitz nonzero differentiable supported nonpos).flow t Q)
  sigma : ∀ t Q, (descentOf lipschitz nonzero differentiable supported nonpos).flow t ((ambK M).σ Q) =
    (ambK M).σ ((descentOf lipschitz nonzero differentiable supported nonpos).flow t Q)
  strict : ∀ Q : Om n (2 * M), a₀ ≤ penW F (2 * M) 1 Q → penW F (2 * M) 1 Q ≤ b₀ →
    (∀ i, Q.1 ∉ (p i).C) →
    deformed M F p ((descentOf lipschitz nonzero differentiable supported nonpos).flow 1 Q).1 <
      deformed M F p Q.1

theorem exists_global (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F)
    (k N : ι → ℕ) {c η a₀ b₀ δ : ℝ} {d : ι → Packet n (2 * M)}
    (hd : ∀ i, Spec F hfin (s i) (hs i) (k i) (N i) c η (d i))
    (hkn : ∀ i, k i * N i = M)
    {U : ι → Set (ZMod (2 * M) → Ambient n)} (hsub : ∀ i, (d i).U ⊆ U i)
    (hUdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUrev : ∀ i j, Disjoint (U i) (revA (2 * M) ⁻¹' U j))
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (Finsler.EnergySphereSmooth.ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    (hshort : ∀ q : ZMod (2 * M) → Sphere n,
      PolygonDescent.energy F (2 * M) q ≤ b₀ → ShortPolygon δ q)
    (hcover : ∀ q : ZMod (2 * M) → Sphere n, a₀ ≤ PolygonDescent.energy F (2 * M) q →
      PolygonDescent.energy F (2 * M) q ≤ b₀ → PolyCritical F (2 * M) q →
      ∃ p : ι × Bool, (incl q : Om n (2 * M)).1 ∈
        sampleSet (2 * M) (circle F c (s p.1, p.2))) :
    Nonempty (Global M F (packetFamily M d) a₀ b₀) := by
  classical
  let P := packetFamily M d
  have han := family_analytic M F hfin s hs k N hd
  choose hU hUr hW hle hlt hT hTU hβT hβd hβb hβle hβlt
    hbig hsmall hsb hbT hCs hCU hΓT hC using han
  have hhalf := family_half M F hfin s hs k N hd hkn
  let r := revA (n := n) (2 * M)
  let h := rotA (n := n) (2 * M) (M : ZMod (2 * M))
  have hr := revA_revA (n := n) (2 * M)
  have hTr : ∀ p x, x ∈ (P p).T → r x ∈ (P (Finsler.ReversalFamily.flip p)).T := by
    rintro ⟨i, o⟩ x hx
    cases o
    · exact hx
    · change r (r x) ∈ (d i).T
      rwa [hr]
  have hTh : ∀ p x, x ∈ (P p).T → h x ∈ (P p).T := fun p x hx => (hhalf p).2.1 x |>.mpr hx
  have hWr : ∀ p x, x ∈ (P p).T →
      (P (Finsler.ReversalFamily.flip p)).W (r x) = r ((P p).W x) := by
    rintro ⟨i, o⟩ x _
    cases o <;> simp [P, packetFamily, Finsler.ReversalFamily.flip, reversePacket, revField, hr, r]
  have hWh : ∀ p x, x ∈ (P p).T → (P p).W (h x) = h ((P p).W x) :=
    fun p x hx => (hhalf p).2.2.1 x (hTU p hx)
  have hβrev : ∀ p x, (P p).β (r x) = (P (Finsler.ReversalFamily.flip p)).β x := by
    rintro ⟨i, o⟩ x
    cases o <;> simp [P, packetFamily, Finsler.ReversalFamily.flip, reversePacket,
      Finsler.InvolutionConjugacy.conjFun, hr, r]
  have hβr : ∀ x, (∑ p, (P p).β (r x)) = ∑ p, (P p).β x := by
    intro x
    simp only [hβrev]
    exact Equiv.sum_comp Finsler.ReversalFamily.flip (fun p => (P p).β x)
  have hβh : ∀ x, (∑ p, (P p).β (h x)) = ∑ p, (P p).β x := by
    intro x
    exact Finset.sum_congr rfl fun p _ => (hhalf p).2.2.2.1 x
  have hcrit : ∀ q : ZMod (2 * M) → Sphere n, a₀ ≤ PolygonDescent.energy F (2 * M) q →
      PolygonDescent.energy F (2 * M) q ≤ b₀ → PolyCritical F (2 * M) q →
      (incl q : Om n (2 * M)).1 ∈ ⋃ p, (P p).T := by
    intro q h1 h2 h3
    obtain ⟨p, hp⟩ := hcover q h1 h2 h3
    exact mem_iUnion.mpr ⟨p, hΓT p hp⟩
  obtain ⟨V, KL, hL, hV0, hg, hsupp, hVle, hVT, hρ, hσ, hstrict⟩ :=
    exists_level_descent_K M F hn hδ hshort Finsler.ReversalFamily.flip
      hU hUr (family_disjoint M hsub hUdis hUrev) hW hle hlt hT hTU
      hTr hTh hWr hWh hβT hβd hβr hβh hβle hβlt hcrit
  exact ⟨⟨V, KL, hL, hV0, hg, hsupp, hVle, hVT, hρ, hσ, hstrict⟩⟩

/-- Simultaneous actual-circle selection followed by global K descent, with the geometric
neighbourhood separation and critical-circle coverage left as explicit inputs. -/
theorem exists_finite_global (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F) (k : ι → ℕ)
    (hkc : ∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (Finsler.CriticalLevels.chosen F (s i) (hs i)).loop) = c) :
    ∃ L M₀ : ℕ, 0 < L ∧ (∀ i, k i ∣ L) ∧ ∀ M' : ℕ, M₀ ≤ M' → L ∣ M' → ∀ [NeZero M']
      {a₀ b₀ δ : ℝ},
      (∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
        ContDiffAt ℝ 1 (Finsler.EnergySphereSmooth.ambientMinEnergy F)
          ((P : Ambient n), (Q : Ambient n))) →
      (∀ q : ZMod (2 * M') → Sphere n,
        PolygonDescent.energy F (2 * M') q ≤ b₀ → ShortPolygon δ q) →
      ∀ U : ι → Set (ZMod (2 * M') → Ambient n), (∀ i, IsOpen (U i)) →
      (∀ i, ∀ u ∈ posCircle F c (s i), amb (Finsler.PolygonSampling.samplePoly (2 * M') u) ∈ U i) →
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
      (∀ i j, Disjoint (U i) (revA (2 * M') ⁻¹' U j)) →
      (∀ q : ZMod (2 * M') → Sphere n, a₀ ≤ PolygonDescent.energy F (2 * M') q →
        PolygonDescent.energy F (2 * M') q ≤ b₀ → PolyCritical F (2 * M') q →
        ∃ p : ι × Bool, (incl q : Om n (2 * M')).1 ∈
          sampleSet (2 * M') (circle F c (s p.1, p.2))) →
      ∀ {η : ℝ}, 0 < η → ∃ d : ι → Packet n (2 * M'),
        (∀ i, (d i).U ⊆ U i ∧ Spec F hfin (s i) (hs i) (k i) (M' / k i) c η (d i)) ∧
        Nonempty (Global M' F (packetFamily M' d) a₀ b₀) := by
  obtain ⟨L, M₀, hL, hkL, hdata⟩ := exists_finite_circle_packets F hn hfin hc s hs k hkc
  refine ⟨L, M₀, hL, hkL, fun M' hM hLM _ a₀ b₀ δ hδ hshort U hU hΓ hUdis hUrev hcover η hη => ?_⟩
  obtain ⟨d, hd⟩ := hdata M' hM hLM U hU hΓ hη
  have hkn : ∀ i, k i * (M' / k i) = M' := fun i => Nat.mul_div_cancel' ((hkL i).trans hLM)
  exact ⟨d, hd, exists_global M' F hn hfin s hs k (fun i => M' / k i)
    (fun i => (hd i).2) hkn (fun i => (hd i).1) hUdis hUrev hδ hshort hcover⟩

end

end Finsler.CirclePacketFamily
