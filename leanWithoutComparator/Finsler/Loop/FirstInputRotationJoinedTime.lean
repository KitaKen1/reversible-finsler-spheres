module

public import Finsler.Loop.FirstInputRotationUniformFullTime
public import Finsler.Loop.CompactJoinCapLocalization
public import Finsler.Loop.DegreeLoweringComposition

/-! Keep the genuine first join cap through the full cut-time
rotation comparison. Both sides are actual ordinary-input operations
and take values in the identical retained-length sublevel. -/

@[expose] public section
namespace Finsler.FirstInputRotationJoinedTime

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
  {κ R : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hR : R ≤ 1 / 2)
  {r : ℝ} (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (F : ReversibleMetric (m + 1))
  (B η : ℝ) (hη : 0 < η) (hρr : ρ < r)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def joined (s : _root_.unitInterval) :
    DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) ((m + 1) + (m + p)) :=
  DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR)
    (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F B η hη hρr hgood hT s)

theorem homology_eq (q : ℕ) :
    (joined α β hκ hκR hR hr p T h F B η hη hρr hgood hT 0).homology q =
      (joined α β hκ hκR hR hr p T h F B η hη hρr hgood hT 1).homology q := by
  simp only [joined, DegreeLoweringComposition.homology]
  rw [FirstInputRotationTimeEndpoints.homology_eq]

theorem component_normal (s : _root_.unitInterval) (q : ℕ) :
    (joined α β hκ hκR hR hr p T h F B η hη hρr hgood hT s).component q =
      eqToHom (congrArg (chains (TopCat.of (P × Q))).X (Nat.add_assoc (m + 1) (m + p) q)) ≫
        (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR).component ((m + p) + q) ≫
          AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
            (push (FirstInputRotationTimeEndpoints.cylinderSlice α β R s)).f ((m + p) + q + 1) ≫
              ClosedCapDegreeTransport.align m p
                (FirstInputRotationFullTime.retracted α β R r hR hr p T h F B η hη hρr hgood hT) q ≫
                  (push (FirstInputRotationFilteredCap.retained α β R r hR hr F B)).f q := by
  rw [joined, DegreeLoweringComposition.component, FirstInputRotationTimeEndpoints.component_normal]

theorem exists_uniform [CompactSpace P] [CompactSpace Q]
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r < 1)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (hb : 0 < b)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ R > 0, ∃ hR : R ≤ 1 / 2, ∃ κ : ℝ, ∃ hκ : 0 < κ, ∃ hκR : 2 * κ ≤ R,
      ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧
      ∀ (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
        (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
        (∀ x y, SobolevLength.length F (α x) + SobolevLength.length F (β y) < A) →
        ∃ hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η p T,
        ∀ q,
          (joined α β hκ hκR hR hr p T h F (A - L + 5 * ε) η hη hρr hgood hT 0).homology q =
          (joined α β hκ hκR hR hr p T h F (A - L + 5 * ε) η hη hρr hgood hT 1).homology q := by
  obtain ⟨u, hu, _hu1, hscale⟩ := FirstInputRotationUniformFullTime.exists_uniform α β h hρr hr F hε hb hradius
  let R : ℝ := min (u / 2) (1 / 4)
  have hR0 : 0 < R := lt_min (half_pos hu) (by norm_num)
  have hR1 : R ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hRu : R < u := (min_le_left _ _).trans_lt (by linarith)
  let κ : ℝ := R / 4
  have hκ0 : 0 < κ := div_pos hR0 (by norm_num)
  have hκR0 : 2 * κ ≤ R := by dsimp only [κ]; linarith
  obtain ⟨η, _hη0, hη0, hηb, had⟩ := hscale R hR1 hRu
  refine ⟨R, hR0, hR1, κ, hκ0, hκR0, η, hη0, hηb, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨hg, _he⟩ := had p L A T hT hshort (fun z => hA z.val.1 z.val.2)
  exact ⟨hg, homology_eq α β hκ0 hκR0 hR1 hr p T h F (A - L + 5 * ε) η hη0 hρr hg hT⟩

end
end Finsler.FirstInputRotationJoinedTime
