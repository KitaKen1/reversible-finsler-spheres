module

public import Finsler.Loop.NativeOrderedDoubleCutDiagonal
public import Finsler.Topology.NormalizedSelfCut

/-! Genuine common ordered-near input. Both original Thom factors and
both SAME genuine GH-power tests use actual maps, with arbitrary last
closed test. Closure and literal diagonal vanishing hold on this LOCAL
near-domain. Global supported gluing is a separate construction. -/
@[expose] public section
namespace Finsler.NativeOrderedDoubleCutCochain
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.H1SelfCutNeighborhood
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

abbrev domain := NativeOrderedDoubleCutGeometry.domain (m + 1) (NativeClosingArcPowerVanishing.radius m hm F)

def firstOutput : domain m hm F ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => left (NativeOrderedDoubleCutGeometry.firstCut (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z),
    (continuous_left (n := m + 1)).comp (NativeOrderedDoubleCutGeometry.continuous_firstCut _)⟩

def lastOutput : domain m hm F ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => right (NativeOrderedDoubleCutGeometry.lastCut (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z),
    (continuous_right (n := m + 1)).comp (NativeOrderedDoubleCutGeometry.continuous_lastCut _)⟩

def firstParameter : domain m hm F ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  SupportedCap.subspaceMap (NativeOrderedDoubleCutGeometry.source (m + 1))
    (NativeOrderedDoubleCutGeometry.near (m + 1) (NativeClosingArcPowerVanishing.radius m hm F)) ≫
      NativeOrderedDoubleCutGeometry.firstParameter (m + 1)

def lastParameter : domain m hm F ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  SupportedCap.subspaceMap (NativeOrderedDoubleCutGeometry.source (m + 1))
    (NativeOrderedDoubleCutGeometry.near (m + 1) (NativeClosingArcPowerVanishing.radius m hm F)) ≫
      NativeOrderedDoubleCutGeometry.lastParameter (m + 1)

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def tests : singularCochainGroup (ZMod 2) (domain m hm F)
    (NativeGHPowers.degree m a + (NativeGHPowers.degree m b + k)) :=
  cochainCup _ _
    (cochainPullback (firstOutput m hm F) _ (NativeClosingArcPowerVanishing.powerCocycle m hm F a))
    (cochainCup _ _
      (cochainPullback (NativeOrderedDoubleCutDiagonal.middleMap m hm F) _
        (NativeClosingArcPowerVanishing.powerCocycle m hm F b))
      (cochainPullback (lastOutput m hm F) k E))

theorem tests_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (domain m hm F) _ (tests m hm F a b k E) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _
    (pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a))
    (cochainCupZMod2_respects_cocycles _ _ _ _
      (pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b))
      (pullback_closed _ k E hE))

theorem tests_diagonal_zero :
    cochainPullback (NativeOrderedDoubleCutDiagonal.inclusion (m + 1)
      (NativeClosingArcPowerVanishing.radius m hm F)) _ (tests m hm F a b k E) = 0 := by
  have hz := NativeOrderedDoubleCutDiagonal.middle_literal_zero m hm F b
  rw [pullback_comp] at hz
  rw [tests, cochainCup_naturality, cochainCup_naturality, hz,
    cochainCup_zero_left, cochainCup_zero_right]

variable {ρ : ℝ} (hρ : 0 < ρ)

def raw : singularCochainGroup (ZMod 2) (domain m hm F)
    ((m + 1) + ((m + 1) + (NativeGHPowers.degree m a + (NativeGHPowers.degree m b + k)))) :=
  cochainCup _ _
    (cochainPullback (firstParameter m hm F) (m + 1) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ))
    (cochainCup _ _
      (cochainPullback (lastParameter m hm F) (m + 1) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ))
      (tests m hm F a b k E))

theorem raw_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (domain m hm F) _ (raw m hm F a b k E hρ) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _
    (pullback_closed _ _ _ (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ))
    (cochainCupZMod2_respects_cocycles _ _ _ _
      (pullback_closed _ _ _ (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ))
      (tests_closed m hm F a b k E hE))

theorem raw_diagonal_zero :
    cochainPullback (NativeOrderedDoubleCutDiagonal.inclusion (m + 1)
      (NativeClosingArcPowerVanishing.radius m hm F)) _ (raw m hm F a b k E hρ) = 0 := by
  rw [raw, cochainCup_naturality, cochainCup_naturality, tests_diagonal_zero,
    cochainCup_zero_right, cochainCup_zero_right]

def cocycle := SingularNormalization.normalize (domain m hm F) _ (raw m hm F a b k E hρ)

theorem cocycle_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (domain m hm F) _ (cocycle m hm F a b k E hρ) = 0 :=
  SingularNormalization.normalize_closed _ _ _ (raw_closed m hm F a b k E hρ hE)

theorem cocycle_normalized : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (domain m hm F)) (cocycle m hm F a b k E hρ) :=
  SingularNormalization.normalize_degeneracies _ _ _

theorem cocycle_diagonal_zero :
    cochainPullback (NativeOrderedDoubleCutDiagonal.inclusion (m + 1)
      (NativeClosingArcPowerVanishing.radius m hm F)) _ (cocycle m hm F a b k E hρ) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (raw_diagonal_zero m hm F a b k E hρ)

end
end Finsler.NativeOrderedDoubleCutCochain
