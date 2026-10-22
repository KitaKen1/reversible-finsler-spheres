module

public import Finsler.Loop.NativeSequentialTriplePrism
public import Finsler.Loop.NativeClosingArcPowerVanishing
public import Finsler.Loop.HomotopyRangeRestriction

/-! The SAME genuine first/middle GH-power representatives on the
ACTUAL triple of loops, with an arbitrary closed last test. Literal
zero on the true short-middle subspace kills the ORIGINAL singular
prism whenever its WHOLE homotopy family lies there, also relatively
on any genuine source carrier. No pointwise-to-cochain shortcut. -/
@[expose] public section
namespace Finsler.NativeTripleGHTest
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialTripleComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

def first (n : ℕ) : triple n ⟶ Loops n := TopCat.ofHom ⟨fun z => z.1, continuous_fst⟩
def middle (n : ℕ) : triple n ⟶ Loops n := TopCat.ofHom ⟨fun z => z.2.1, continuous_fst.comp continuous_snd⟩
def last (n : ℕ) : triple n ⟶ Loops n := TopCat.ofHom ⟨fun z => z.2.2, continuous_snd.comp continuous_snd⟩

def short {n : ℕ} (F : ReversibleMetric n) (L : ℝ) : Set (triple n) :=
  middle n ⁻¹' SelfCutOscillation.short F L

theorem short_open {n : ℕ} (F : ReversibleMetric n) (L : ℝ) : IsOpen (short F L) :=
  isOpen_lt ((SelfCutOscillation.continuous_length F).comp (middle n).hom.continuous) continuous_const

theorem middle_zero {n : ℕ} (F : ReversibleMetric n) (L : ℝ) (p : ℕ)
    (B : singularCochainGroup (ZMod 2) (Loops n) p)
    (hB : cochainPullback (LengthFilteredLoopRotation.full F L) p B = 0) :
    cochainPullback (SupportedCap.subspaceMap (triple n) (short F L)) p
      (cochainPullback (middle n) p B) = 0 :=
  pullback_support (middle n) (short F L) (SelfCutOscillation.short F L) (fun _ h => h) p B hB

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

abbrev degree := NativeGHPowers.degree m a + (NativeGHPowers.degree m b + k)

def test : singularCochainGroup (ZMod 2) (triple (m + 1)) (degree m a b k) :=
  cochainCup _ _
    (cochainPullback (first (m + 1)) _ (NativeClosingArcPowerVanishing.powerCocycle m hm F a))
    (cochainCup _ _
      (cochainPullback (middle (m + 1)) _ (NativeClosingArcPowerVanishing.powerCocycle m hm F b))
      (cochainPullback (last (m + 1)) k E))

theorem test_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (triple (m + 1)) _ (test m hm F a b k E) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _
    (pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a))
    (cochainCupZMod2_respects_cocycles _ _ _ _
      (pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b))
      (pullback_closed _ _ E hE))

theorem test_short_zero :
    cochainPullback (SupportedCap.subspaceMap (triple (m + 1))
      (short F (NativeClosingArcPowerVanishing.supportScale m hm F))) _ (test m hm F a b k E) = 0 := by
  rw [test, cochainCup_naturality, cochainCup_naturality,
    middle_zero F _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_supported m hm F b),
    cochainCup_zero_left, cochainCup_zero_right]

section Prism
variable {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
  (K : Set Y) (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1))

theorem prism_zero (hH : ∀ z : _root_.unitInterval × X, H z ∈ K)
    (hT : cochainPullback (SupportedCap.subspaceMap Y K) (q + 1) T = 0) :
    NativeSequentialTriplePrism.primitive H q T = 0 := by
  change (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ T = 0
  rw [← HomotopyRangeRestriction.include_prism H K hH q, Category.assoc]
  change ((HomotopyRangeRestriction.restriction H K hH).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
    cochainPullback (SupportedCap.subspaceMap Y K) (q + 1) T = 0
  rw [hT, comp_zero]

theorem primitive_carrier_zero (C : Set X)
    (hH : ∀ (s : _root_.unitInterval) (x : C), H (s, x.val) ∈ K)
    (hT : cochainPullback (SupportedCap.subspaceMap Y K) (q + 1) T = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) q (NativeSequentialTriplePrism.primitive H q T) = 0 := by
  let e := SupportedCap.subspaceMap X C
  have hz := prism_zero (H.comp (TopCat.Homotopy.refl e)) K q T (fun z => hH z.1 z.2) hT
  change (push e).f q ≫ ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ T) = 0
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  exact hz
end Prism

end
end Finsler.NativeTripleGHTest
