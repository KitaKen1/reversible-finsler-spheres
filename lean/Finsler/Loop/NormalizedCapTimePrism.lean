module

public import Finsler.Loop.NormalizedCapRightInterval
public import Finsler.Loop.CompactJoinCocycle
public import Finsler.Topology.SingularTimeCylinderMaps

/-! The actual normalized join cap commutes with the original full
product-time prism. Prove the genuine time-coordinate diagrams and
use actual cap naturality and the exact interval-cross identity.
There is no assumed cap/time comparison or homology injectivity. -/

@[expose] public section
namespace Finsler.NormalizedCapTimePrism

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.IntervalSobolev
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem homotopy_cap {X Z : TopCat.{0}} {f g : X ⟶ Z}
    (H : TopCat.Homotopy f g) (j : Z ⟶ X)
    (hj : H.h ≫ j = CartesianMonoidalCategory.fst X TopCat.I)
    (a q : ℕ) (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (H.toSSet.chainComplexMap coeff).hom (a + q) (a + q + 1) ≫
      absoluteChain Z a (q + 1) (a + q + 1) (by omega) (cochainPullback j a φ) =
      absoluteChain X a q (a + q) rfl φ ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) := by
  have hp : cochainPullback H.h a (cochainPullback j a φ) =
      cochainPullback (CartesianMonoidalCategory.fst X TopCat.I) a φ := by
    rw [← pullback_comp, hj]
  have hn : (push H.h).f (a + q + 1) ≫
      absoluteChain Z a (q + 1) (a + q + 1) (by omega) (cochainPullback j a φ) =
      absoluteChain (X ⊗ TopCat.I) a (q + 1) (a + q + 1) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X TopCat.I) a φ) ≫ (push H.h).f (q + 1) := by
    have he := (RelativeCapBoundary.absolute_chain_natural H.h a (q + 1)
      (a + q + 1) (by omega) (cochainPullback j a φ)).symm
    rw [hp] at he
    exact he
  rw [← TimeShuffleComparison.rectangle_eq_prism H (a + q),
    ← TimeShuffleComparison.rectangle_eq_prism H q]
  change (TimeTriangleSplit.interval X (a + q) ≫ (push H.h).f (a + q + 1)) ≫ _ =
    absoluteChain X a q (a + q) rfl φ ≫ (TimeTriangleSplit.interval X q ≫ (push H.h).f (q + 1))
  rw [Category.assoc, hn, ← Category.assoc, NormalizedCapRightInterval.interval_cap X a q φ hφ,
    Category.assoc]

def spatial (X : TopCat.{0}) : TopCat.of (ClosedInterval × X) ⟶ X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

theorem annular_cap (X : TopCat.{0}) (a q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    AnnularTimeTrim.prism X (a + q) ≫
      absoluteChain (TopCat.of (ClosedInterval × X)) a (q + 1) (a + q + 1) (by omega)
        (cochainPullback (spatial X) a φ) =
      absoluteChain X a q (a + q) rfl φ ≫ AnnularTimeTrim.prism X q := by
  apply homotopy_cap (AnnularTimeTrim.cylinder X) (spatial X) ?_ a q φ hφ
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem original_second_half_cap {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    (a q : ℕ) (φ : singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (TopCat.of (P × Q))) φ) :
    (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom (a + q) (a + q + 1) ≫
      absoluteChain (TopCat.of (P × (ClosedInterval × Q))) a (q + 1) (a + q + 1) (by omega)
        (cochainPullback (CompactJoinCocycle.timeProjection (P := P) (Q := Q)) a φ) =
      absoluteChain (TopCat.of (P × Q)) a q (a + q) rfl φ ≫
        (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom q (q + 1) := by
  rw [← SingularTimeCylinderMaps.product_original (a + q), ← SingularTimeCylinderMaps.product_original q]
  apply homotopy_cap (SingularTimeCylinderMaps.cylinder (TopCat.of P) (TopCat.of Q))
    (CompactJoinCocycle.timeProjection (P := P) (Q := Q)) ?_ a q φ hφ
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem actual_join_cap {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
    (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (hn : 1 ≤ n)
    {ρ : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom (n + q) (n + q + 1) ≫
      absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n (q + 1) (n + q + 1) (by omega)
        (CompactJoinCocycle.timeCocycle α β hn hρ) =
      absoluteChain (TopCat.of (P × Q)) n q (n + q) rfl (CompactJoinCocycle.cocycle α β hn hρ) ≫
        (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom q (q + 1) :=
  original_second_half_cap n q (CompactJoinCocycle.cocycle α β hn hρ)
    (CompactJoinCocycle.cocycle_normalized α β hn hρ)

end
end Finsler.NormalizedCapTimePrism
