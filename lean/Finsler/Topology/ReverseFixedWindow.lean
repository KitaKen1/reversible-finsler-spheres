module

public import Finsler.Topology.CircleRootWindow
public import Finsler.Topology.FixedLensConjugacy

/-! reverse a complete local label packet, retaining its root
bound and all ordinary lens estimates. -/

@[expose] public section

namespace Finsler.ReverseFixedWindow

open Set Module Finsler.SphereGeometry Finsler.Geometry
open Finsler.CircleRootWindow Finsler.LocalLabelReverse Finsler.LocalLabelPacket Finsler.InvolutionConjugacy Finsler.EquivariantField
open Finsler.RevLabel Finsler.ReversalLabelData Finsler.AmbientK Finsler.SampleK
open Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.PolygonDescentK
open Finsler.AmbientDescent Finsler.FlowLens Finsler.LensContinuation Finsler.LevelField
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open scoped ContDiff NNReal
noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1000000

variable {n : ℕ} (M : ℕ) [NeZero M]

theorem reverse_window (F : ReversibleMetric n) {A I : ℕ} {c : ℝ} {d : Packet n (2 * M)}
    (hd : Window F (M : ZMod (2 * M)) A I c d) :
    Window F (M : ZMod (2 * M)) A I c (reversePacket M d) := by
  intro V KL hL hV0 g O hg hsupp hle hVT hgT a₀ b₀ ha hb R hR hdis hgc hband hstrict
  let r := revA (n := n) (2 * M)
  let ρ := (ambK (n := n) M).ρ
  have hr : ∀ y, r (r y) = y := revA_revA _
  let gp := conjFun r g
  have hgp : ∀ P ∈ r ⁻¹' O, DifferentiableAt ℝ gp P :=
    fun P hP => (hg (r P) hP).comp P r.differentiableAt
  have hsp : ∀ P, revField V P ≠ 0 → P ∈ r ⁻¹' O := by
    intro P hP
    apply hsupp (r P)
    intro he
    exact hP (by change r (V (r P)) = 0; rw [he, map_zero])
  have hlep : ∀ P ∈ r ⁻¹' O, fderiv ℝ gp P (revField V P) ≤ 0 := by
    intro P hP
    change fderiv ℝ (conjFun r g) P (conjField r V P) ≤ 0
    rw [conj_derivative r hr (hg (r P) hP) V]
    exact hle _ hP
  let Dp := descentOf (lipschitz_revField hL) (revField_ne_zero hV0) hgp hsp hlep
  let D := descentOf hL hV0 hg hsupp hle
  have hfun : ∀ Q : Om n (2 * M), g (ρ Q).1 = gp Q.1 := fun _ => rfl
  have hflow : ∀ t Q, D.flow t (ρ Q) = ρ (Dp.flow t Q) := by
    intro t Q
    have he := flowOm_revField hL hV0 t (ρ Q)
    change Dp.flow t (ρ (ρ Q)) = ρ (D.flow t (ρ Q)) at he
    rw [(ambK M).ρρ] at he
    have he' := congrArg ρ he
    rw [(ambK M).ρρ] at he'
    exact he'.symm
  have hUV : ∀ Q : Om n (2 * M), Q ∈ d.big ↔ ρ Q ∈ (reversePacket M d).big := by
    intro Q
    change Q ∈ d.big ↔ ρ (ρ Q) ∈ d.big
    rw [(ambK M).ρρ]
  have hWp : ∀ y ∈ d.T, revField V y = d.W y := by
    intro y hy
    have hmem : r y ∈ (reversePacket M d).T := by change r (r y) ∈ d.T; rwa [hr]
    change r (V (r y)) = d.W y
    rw [hVT _ hmem]
    change r (r (d.W (r (r y)))) = d.W y
    rw [hr, hr]
  have hgpT : ∀ y ∈ d.T, gp y = pen F (2 * M) 1 y + d.β y := by
    intro y hy
    have hmem : r y ∈ (reversePacket M d).T := by change r (r y) ∈ d.T; rwa [hr]
    change g (r y) = _
    rw [hgT _ hmem]
    change pen F (2 * M) 1 (r y) + d.β (r (r y)) = _
    rw [pen_revA, hr]
  have hcgp : Continuous (fun Q : Om n (2 * M) => gp Q.1) := hgc.comp ρ.continuous
  have hbp : IsCompact {Q : Om n (2 * M) | a₀ ≤ gp Q.1 ∧ gp Q.1 ≤ b₀} :=
    (reversalHomeo M).isCompact_preimage.mpr hband
  have hdisp : Disjoint d.big (ρ ⁻¹' R) := by
    apply Set.disjoint_left.mpr
    intro Q hQ hQR
    exact Set.disjoint_left.mp hdis ((hUV Q).mp hQ) hQR
  have hstrictp : ∀ Q : Om n (2 * M), a₀ ≤ gp Q.1 → gp Q.1 ≤ b₀ →
      Q ∉ d.small ∪ (ρ ⁻¹' R) → gp (Dp.flow 1 Q).1 < gp Q.1 := by
    intro Q h1 h2 hQ
    have hn : ρ Q ∉ (reversePacket M d).small ∪ R := by
      intro h
      apply hQ
      rcases h with h | h
      · left
        change ρ (ρ Q) ∈ d.small at h
        rwa [(ambK M).ρρ] at h
      · exact Or.inr h
    have h := hstrict (ρ Q) h1 h2 hn
    rw [hflow] at h
    exact h
  obtain ⟨e, he, hmodel⟩ := hd (lipschitz_revField hL) (revField_ne_zero hV0) hgp hsp hlep
    hWp hgpT ha hb (hR.preimage ρ.continuous) hdisp hcgp hbp hstrictp
  let Z : Set (Om n (2 * M)) := {Q | rotA (2 * M) (M : ZMod (2 * M)) Q.1 = Q.1}
  have hZ : ∀ Q : Om n (2 * M), Q ∈ Z ↔ ρ Q ∈ Z := by
    intro Q
    change ((ambK M).σ Q).1 = Q.1 ↔ ((ambK M).σ (ρ Q)).1 = (ρ Q).1
    constructor
    · intro h
      have h' : (ambK M).σ Q = Q := Subtype.ext h
      have he : (ambK M).σ (ρ Q) = ρ Q := by rw [← (ambK M).ρσ, h']
      exact congrArg Subtype.val he
    · intro h
      have h' : (ambK M).σ (ρ Q) = ρ Q := Subtype.ext h
      have he := congrArg ρ h'
      change (ambK M).ρ ((ambK M).σ (ρ Q)) = (ambK M).ρ (ρ Q) at he
      rw [(ambK M).ρσ, (ambK M).ρρ] at he
      exact congrArg Subtype.val he
  refine ⟨e, he, fun a b t ht ha' hb' hab => ?_⟩
  obtain ⟨hf, hz⟩ := hmodel a b t ht ha' hb' hab
  have heq := fun q => Finsler.FixedLensConjugacy.nonempty_part_equiv
    Dp D (reversalHomeo M) hfun hflow hUV hZ a b t q
  constructor
  · intro q
    obtain ⟨equiv⟩ := heq q
    have := hf q
    exact Module.Finite.equiv equiv
  · intro q hq z
    obtain ⟨equiv⟩ := heq q
    have he := congrArg equiv (hz q hq (equiv.symm z))
    simpa only [equiv.apply_symm_apply, map_zero] using he

end

end Finsler.ReverseFixedWindow

