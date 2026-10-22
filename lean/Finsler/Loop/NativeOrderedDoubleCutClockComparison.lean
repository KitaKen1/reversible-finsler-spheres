module

public import Finsler.Loop.NativeOrderedDoubleCutSupported
public import Finsler.Loop.OrderedClockCycleComparison
public import Finsler.Loop.CochainDegreeTransport
public import Finsler.Loop.MeridianThetaCutCoefficient

/-! Install the GENUINE GLOBAL common supported double-Thom/test
input in the already proved raw-clock cycle comparison. Its diagonal
support is DISCHARGED by the two actual supported caps. All actual
degree transports are retained. Original sequential-cap/output
reparametrization alignment remains a separate unproved comparison. -/
@[expose] public section
namespace Finsler.NativeOrderedDoubleCutClockComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

abbrev clockDegree := NativeOrderedDoubleCutSupported.totalDegree m a b k - 3

include hm in
theorem degree_match : clockDegree m a b k + 3 = NativeOrderedDoubleCutSupported.totalDegree m a b k := by
  dsimp [clockDegree, NativeOrderedDoubleCutSupported.totalDegree]
  omega

def input : singularCochainGroup (ZMod 2)
    (Loops (m + 1) ⊗ OrderedDoubleCutTimes.space) (clockDegree m a b k + 3) :=
  CochainDegreeTransport.pre (NativeOrderedDoubleCutSupported.source m) (degree_match m hm a b k)
    (NativeOrderedDoubleCutSupported.cochain m hm F a b k E)

theorem input_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1) ⊗ OrderedDoubleCutTimes.space) _ (input m hm F a b k E) = 0 :=
  CochainDegreeTransport.closed _ _ _ (NativeOrderedDoubleCutSupported.cochain_closed m hm F a b k E hE)

def diagonalLift : Loops (m + 1) ⊗ TopCat.I.{0} ⟶
    TopCat.of (NativeOrderedDoubleCutSupported.diagonal m) := TopCat.ofHom
  ⟨fun z => ⟨(Loops (m + 1) ◁ OrderedDoubleCutTriangle.diagonal) z, rfl⟩,
    (Loops (m + 1) ◁ OrderedDoubleCutTriangle.diagonal).hom.continuous.subtype_mk _⟩

theorem diagonal_factor : diagonalLift m ≫
    SupportedCap.subspaceMap (NativeOrderedDoubleCutSupported.source m) (NativeOrderedDoubleCutSupported.diagonal m) =
      Loops (m + 1) ◁ OrderedDoubleCutTriangle.diagonal := rfl

theorem pullback_pre_zero {X Y : TopCat.{0}} {i j : ℕ} (h : i = j) (f : X ⟶ Y)
    (φ : singularCochainGroup (ZMod 2) Y j) (hz : cochainPullback f j φ = 0) :
    cochainPullback f i (CochainDegreeTransport.pre Y h φ) = 0 := by
  subst j
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using hz

theorem input_diagonal_zero :
    cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTriangle.diagonal) _ (input m hm F a b k E) = 0 := by
  apply pullback_pre_zero
  rw [← diagonal_factor, pullback_comp, NativeOrderedDoubleCutSupported.cochain_diagonal_zero]
  change (push (diagonalLift m)).f _ ≫ 0 = 0
  exact comp_zero

def primitive := OrderedClockCycleComparison.primitive (Loops (m + 1)) (clockDegree m a b k)
  (input m hm F a b k E)

theorem comparison_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) _ (primitive m hm F a b k E) =
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b k + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.leftClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b k E)) -
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b k + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.rightClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b k E)) :=
  OrderedClockCycleComparison.comparison_boundary _ _ _ (input_closed m hm F a b k E hE)
    (input_diagonal_zero m hm F a b k E)

theorem cycles_equal (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    (chains (Loops (m + 1))).iCycles (clockDegree m a b k + 1) ≫
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b k + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.leftClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b k E)) =
    (chains (Loops (m + 1))).iCycles (clockDegree m a b k + 1) ≫
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b k + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.rightClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b k E)) :=
  OrderedClockCycleComparison.cycles_equal _ _ _ (input_closed m hm F a b k E hE)
    (input_diagonal_zero m hm F a b k E)

theorem cycle_values_equal (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (clockDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (clockDegree m a b k + 1) (clockDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b k + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.leftClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b k E)) =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b k + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.rightClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b k E)) :=
  OrderedClockCycleComparison.cycle_values_equal _ _ _ (input_closed m hm F a b k E hE)
    (input_diagonal_zero m hm F a b k E) c hc

def evaluation : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + 1) :=
  classRepr (Loops (m + 1)) (m + 1) (MeridianThetaCutCoefficient.evaluationClass m)

theorem evaluation_closed : cochainCoboundary (ZMod 2) (Loops (m + 1)) (m + 1) (evaluation m) = 0 :=
  classRepr_isCocycle _ _ _

theorem evaluation_cycles_equal :
    (chains (Loops (m + 1))).iCycles (clockDegree m a b (m + 1) + 1) ≫
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b (m + 1) + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.leftClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b (m + 1) (evaluation m))) =
    (chains (Loops (m + 1))).iCycles (clockDegree m a b (m + 1) + 1) ≫
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (clockDegree m a b (m + 1) + 1) ≫
        cochainPullback (Loops (m + 1) ◁ OrderedDoubleCutTimes.rightClock) _
          (SingularNormalization.normalize _ _ (input m hm F a b (m + 1) (evaluation m))) :=
  cycles_equal m hm F a b (m + 1) (evaluation m) (evaluation_closed m)

end
end Finsler.NativeOrderedDoubleCutClockComparison
