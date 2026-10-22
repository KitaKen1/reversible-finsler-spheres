module

public import Finsler.Loop.StartPointCarrierTimeCupZero

/-! The ORIGINAL first normalized Thom cap followed by the ORIGINAL
localized split cup, BEFORE integration over cut time. It vanishes
literally on any carrier whose start OR end is sufficiently far from
the evaluation point. This retains the original subdivision/cap and
works for arbitrary tested cochains, without a cycle premise. -/
@[expose] public section
namespace Finsler.LocalizedParameterCutCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SupportedSelfCut Finsler.SupportedCapNaturality Finsler.LocalizedCutEvaluationCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def cochain (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) ((m + 1) + (p + (m + 1))) :=
  (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) ≫
    GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)

theorem closed (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) ((m + 1) + (p + (m + 1)))
      (cochain m p Q hρ hρr hr hη T) = 0 := by
  have htc := NormalizedSelfCut.testedCocycle_closed (m + 1) p hr T hT
  have hbc := cochainPullback_cocycle (TopCat.ofHom (retained (m + 1) hr)) (m + 1)
    (loopCocycle (m + 1) (by omega) Q hη) (loop_closed (m + 1) (by omega) Q hη)
  have hcup := cochainCupZMod2_respects_cocycles p (m + 1)
    (NormalizedSelfCut.testedCocycle (m + 1) p hr T)
    (cochainPullback (TopCat.ofHom (retained (m + 1) hr)) (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) htc hbc
  exact DegreeLoweringCochainPullback.closed (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr)
    (p + (m + 1)) _ hcup

theorem carrier_zero (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (C : Set (SelfCutThomCocycle.parameters (m + 1)))
    (hC : ∀ z : neighborhood (m + 1) r, z.val ∈ C →
      η ≤ ‖(nearStart (m + 1) r z : Ambient (m + 1)) - (Q : Ambient (m + 1))‖) :
    cochainPullback (SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) C)
      ((m + 1) + (p + (m + 1))) (cochain m p Q hρ hρr hr hη T) = 0 := by
  let X := SelfCutThomCocycle.parameters (m + 1)
  let A := exterior (m + 1) ρ
  let B := neighborhood (m + 1) r
  let f := restriction (SupportedCap.subspaceMap X C) ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)
  have hb : cochainPullback f (m + 1)
      (cochainPullback (TopCat.ofHom (retained (m + 1) hr)) (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) = 0 := by
    rw [retained_pullback, ← pullback_comp]
    exact LocalizedSphereTopCocycle.pullback_far_zero (by omega) Q hη (f ≫ nearStart (m + 1) r)
      (fun x => hC (f x) x.val.property)
  have hc : cochainPullback f (p + (m + 1))
      (GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) = 0 := by
    rw [GeometricTimeCupCochain.splitCup, cochainCup_naturality, hb, cochainCup_zero_right]
  have hz := SupportedCutCochainCarrierZero.subspace_cochain_zero X A B C
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (cover (m + 1) hρr)
    (m + 1) (p + (m + 1)) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) hc
  change (push (SupportedCap.subspaceMap X C)).f ((m + 1) + (p + (m + 1))) ≫
    ((NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) ≫
      GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) = 0
  dsimp only [NormalizedSelfCut.operation, SupportedCapHomology.operation]
  simpa only [Category.assoc] using hz

def farCarrier (n : ℕ) (Q : Sphere n) (D : ℝ) : Set (SelfCutThomCocycle.parameters n) :=
  {z | D ≤ ‖(H1FiberBase.point z.2 : Ambient n) - (Q : Ambient n)‖ ∨
    D ≤ ‖(H1SelfCutNeighborhood.endpoint z : Ambient n) - (Q : Ambient n)‖}

theorem farCarrier_near_start (n : ℕ) (Q : Sphere n) {D r η : ℝ}
    (hr : 0 < r) (hηr : η + r ≤ D) (z : neighborhood n r) (hz : z.val ∈ farCarrier n Q D) :
    η ≤ ‖(nearStart n r z : Ambient n) - (Q : Ambient n)‖ := by
  rcases hz with h | h
  · change η ≤ ‖(H1FiberBase.point z.val.2 : Ambient n) - (Q : Ambient n)‖
    linarith
  · have ht := norm_add_le
      ((H1SelfCutNeighborhood.endpoint z.val : Ambient n) - (H1FiberBase.point z.val.2 : Ambient n))
      ((H1FiberBase.point z.val.2 : Ambient n) - (Q : Ambient n))
    rw [sub_add_sub_cancel] at ht
    have hd : distance n z.val < r := z.property
    change η ≤ ‖(H1FiberBase.point z.val.2 : Ambient n) - (Q : Ambient n)‖
    change ‖(H1SelfCutNeighborhood.endpoint z.val : Ambient n) - (H1FiberBase.point z.val.2 : Ambient n)‖ < r at hd
    linarith

theorem family_zero (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η D : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hηr : η + r ≤ D)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hf : ∀ x, f x ∈ farCarrier (m + 1) Q D) :
    cochainPullback f ((m + 1) + (p + (m + 1))) (cochain m p Q hρ hρr hr hη T) = 0 := by
  let C := farCarrier (m + 1) Q D
  let g : X ⟶ TopCat.of C := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) C := by ext x : 1; rfl
  have hz := carrier_zero m p Q hρ hρr hr hη T C
    (fun z hz => farCarrier_near_start (m + 1) Q (lt_trans hρ hρr) hηr z hz)
  rw [he, pullback_comp, hz]
  simp only [cochainPullback, map_zero]

end
end Finsler.LocalizedParameterCutCochain
