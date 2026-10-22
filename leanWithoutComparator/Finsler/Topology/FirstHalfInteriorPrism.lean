module

public import Finsler.Topology.FirstHalfInteriorFamily
public import Finsler.Topology.TimePrismComparison

/-! The genuine first-half cut domain agrees with the original trimmed
cylinder domain. Its fixed-tested-output deformation has a concrete
prism entirely in the same retained-length sublevel. -/

@[expose] public section
namespace Finsler.FirstHalfInteriorPrism

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SupportedSelfCut Finsler.FirstHalfInteriorFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {X : Type} [TopologicalSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

theorem distance_trimmed (z : ClosedInterval × X) :
    distance n (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le z) =
      distance n (firstParameters u a ha ha1 z) :=
  JoinedHalfCollars.first_distance (InteriorTimeSlide.trimTime a ha.le ha1.le z.1, u z.2)

theorem domain_eq_trimmed (r : ℝ) :
    domain u a ha ha1 r =
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) ⁻¹' neighborhood n r := by
  ext z
  change distance n (firstParameters u a ha ha1 z) < r ↔
    distance n (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le z) < r
  rw [distance_trimmed]

variable {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ)

def endpoint (s : _root_.unitInterval) :
    C(filteredDomain u a ha ha1 hr F A, {w : SphereLoop n | SobolevLength.length F w < A}) :=
  ⟨fun z => filteredFamily u a ha ha1 hr F A (s, z),
    (filteredFamily u a ha ha1 hr F A).continuous.comp (continuous_const.prodMk continuous_id)⟩

def homotopy : TopCat.Homotopy
    (TopCat.ofHom (endpoint u a ha ha1 hr F A 0))
    (TopCat.ofHom (endpoint u a ha ha1 hr F A 1)) where
  toFun := filteredFamily u a ha ha1 hr F A
  continuous_toFun := (filteredFamily u a ha ha1 hr F A).continuous
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem zero_original (z : filteredDomain u a ha ha1 hr F A) :
    (endpoint u a ha ha1 hr F A 0 z).val =
      H1SelfCutNeighborhood.right (FirstHalfJoinedCut.joinedTube (input u a ha ha1 hr z.val)) :=
  congrArg Prod.snd (FirstHalfInteriorFamily.family_zero u a ha ha1 hr z.val)

theorem one_join (z : filteredDomain u a ha ha1 hr F A) :
    (endpoint u a ha ha1 hr F A 1 z).val =
      H1LoopJoin.join (1 / 2) (by norm_num) (by norm_num)
        (H1SelfCutNeighborhood.right (input u a ha ha1 hr z.val).val.1) (u z.val.val.2).val.2
        ((H1SelfCutNeighborhood.basepoint_right (input u a ha ha1 hr z.val).val.1).trans (u z.val.val.2).property) :=
  congrArg Prod.snd (FirstHalfInteriorFamily.family_one u a ha ha1 hr z.val)

def prism (q : ℕ) :
    (chains (TopCat.of (filteredDomain u a ha ha1 hr F A))).X q ⟶
      (chains (TopCat.of {w : SphereLoop n | SobolevLength.length F w < A})).X (q + 1) :=
  ((homotopy u a ha ha1 hr F A).toSSet.chainComplexMap coeff).hom q (q + 1)

theorem prism_boundary (q : ℕ) :
    ((chains (TopCat.of (filteredDomain u a ha ha1 hr F A))).iCycles q ≫
      prism u a ha ha1 hr F A q) ≫
        (chains (TopCat.of {w : SphereLoop n | SobolevLength.length F w < A})).d (q + 1) q =
      (chains (TopCat.of (filteredDomain u a ha ha1 hr F A))).iCycles q ≫
        ((push (TopCat.ofHom (endpoint u a ha ha1 hr F A 0))).f q -
         (push (TopCat.ofHom (endpoint u a ha ha1 hr F A 1))).f q) := by
  exact TimePrismComparison.cycles_prism_boundary
    ((homotopy u a ha ha1 hr F A).toSSet.chainComplexMap coeff) q

end
end Finsler.FirstHalfInteriorPrism
