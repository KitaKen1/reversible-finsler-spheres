module

public import Finsler.Topology.LocalLabelPacket

/-! reverse a complete local label packet, retaining its root
bound and all ordinary lens estimates. -/

@[expose] public section

namespace Finsler.LocalLabelReverse

open Set Module Finsler.SphereGeometry Finsler.Geometry
open Finsler.LocalLabelPacket Finsler.InvolutionConjugacy Finsler.EquivariantField
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

def reversePacket (d : Packet n (2 * M)) : Packet n (2 * M) where
  b := d.b
  r := d.r
  U := revA (2 * M) ⁻¹' d.U
  W := revField d.W
  β := conjFun (revA (2 * M)) d.β
  C := revA (2 * M) ⁻¹' d.C
  T := revA (2 * M) ⁻¹' d.T
  big := (ambK M).ρ ⁻¹' d.big
  small := (ambK M).ρ ⁻¹' d.small

theorem reverse_analytic (F : ReversibleMetric n) {c η : ℝ}
    {Γ : Set (ZMod (2 * M) → Ambient n)} {d : Packet n (2 * M)}
    (hd : Analytic F c η Γ d) :
    Analytic F c η (revA (2 * M) ⁻¹' Γ) (reversePacket M d) := by
  rcases hd with ⟨hU, hUr, hW, hle, hlt, hT, hTU, hβT, hβd, hβb, hβle, hβlt,
    hbig, hsmall, hsb, hbT, hCs, hCU, hΓT, hC⟩
  rcases Finsler.ReversalLabelData.reverse_analytic M F hU hUr hW hle hlt hT hTU hβT
    hβd hβb hβle hβlt with ⟨hU', hUr', hW', hle', hlt', hT', hTU', hβT', hβd', hβb', hβle', hβlt'⟩
  refine ⟨hU', hUr', hW', hle', hlt', hT', hTU', hβT', hβd', hβb', hβle', hβlt',
    hbig.preimage (ambK M).ρ.continuous, hsmall.preimage (ambK M).ρ.continuous,
    preimage_mono hsb, (fun Q hQ => hbT ((ambK M).ρ Q) hQ),
    (fun Q hQ => hCs ((ambK M).ρ Q) hQ), preimage_mono hCU, preimage_mono hΓT, ?_⟩
  intro y hy
  have h := hC (revA (2 * M) y) hy
  rw [pen_revA] at h
  exact h

theorem reverse_half {d : Packet n (2 * M)}
    (hd : HalfInvariant (M : ZMod (2 * M)) d) :
    HalfInvariant (M : ZMod (2 * M)) (reversePacket M d) := by
  rcases hd with ⟨hU, hT, hW, hβ, hbig, hsmall⟩
  have hc := revA_rotA (n := n) (half_shift M)
  refine ⟨preimage_invariant _ _ hc hU, preimage_invariant _ _ hc hT,
    (fun y hy => reverse_half_field M hW hy), conjFun_equivariant _ _ hc hβ, ?_, ?_⟩
  · intro Q
    change (ambK M).ρ ((ambK M).σ Q) ∈ d.big ↔ (ambK M).ρ Q ∈ d.big
    rw [(ambK M).ρσ]
    exact hbig ((ambK M).ρ Q)
  · intro Q
    change (ambK M).ρ ((ambK M).σ Q) ∈ d.small ↔ (ambK M).ρ Q ∈ d.small
    rw [(ambK M).ρσ]
    exact hsmall ((ambK M).ρ Q)

theorem reverse_root_bound (F : ReversibleMetric n) (hfin : (Finsler.Geodesics.primeImages F).Finite)
    {c x : ℝ} {d : Packet n (2 * M)} (hd : RootBound F hfin c x d) :
    RootBound F hfin c x (reversePacket M d) := hd

theorem reverse_model (F : ReversibleMetric n) {c : ℝ} {d : Packet n (2 * M)}
    (hd : Model F c d) : Model F c (reversePacket M d) := by
  intro V KL hL hV0 g O hg hsupp hle hVT hgT a₀ b₀ ha hb hgc hband R hR hdis hstrict
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
    hWp hgpT ha hb hcgp hbp (hR.preimage ρ.continuous) hdisp hstrictp
  refine ⟨e, he, fun a b t ht ha' hb' hab => ?_⟩
  obtain ⟨hrank, hvanish⟩ := hmodel a b t ht ha' hb' hab
  constructor
  · intro j
    exact (Finsler.LensConjugacy.finrank_eq Dp D (reversalHomeo M)
      hfun hflow hUV a b t (j + d.b)).symm.trans (hrank j)
  · intro j hj
    exact (Finsler.LensConjugacy.vanish_iff Dp D (reversalHomeo M)
      hfun hflow hUV a b t j).mp (hvanish j hj)

end

end Finsler.LocalLabelReverse
