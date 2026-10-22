module

public import Finsler.Loop.GeometricTimeCupInterval
public import Finsler.Loop.CochainDegreeTransport

/-! The complete ORIGINAL outer cap/time expression is the existing
geometric time cup, with arbitrary explicit source and near degrees.
This only transports genuine equal degrees and never changes a cut. -/
@[expose] public section
namespace Finsler.GeometricTimeCupSource
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem source_at_degree (m p q N s : ℕ) (hN : N = (m + p) + q) (hs : s = p + q)
    (hP : N + 1 = (m + 1) + s) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q) :
    SelfCutTimePrism.prism (m + 1) N ≫
      CochainDegreeTransport.pre (SelfCutThomCocycle.parameters (m + 1)) hP
        ((NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component s ≫
          CochainDegreeTransport.pre (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) hs
            (GeometricTimeCupCochain.splitCup m p hr T q B)) =
      CochainDegreeTransport.pre (Loops (m + 1)) hN (GeometricTimeCupCochain.cochain m p hρ hρr hr T q B) := by
  subst N s
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp,
    GeometricTimeCupCochain.cochain]
  rw [← SelfCutShuffle.prism_eq_shuffle]

theorem cup_at_degree (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (T : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q) :
    CupOne.cup X p q N h T B = CochainDegreeTransport.pre X h.symm (cochainCup p q T B) := by
  subst N
  rw [CupOne.cup_comparison]
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

end
end Finsler.GeometricTimeCupSource
