module

public import Finsler.Loop.NativeGlobalTimeSquare
public import Finsler.Loop.RelativePrismCochainBoundary
public import Finsler.Topology.RelativeKronecker

/-! Evaluate the genuine double prism against any actual relative
cocycle after any actual map of pairs. This permits changed source
coordinates without asserting that their fundamental input is fixed.
In particular, a zero relative class kills every such input. -/
@[expose] public section
namespace Finsler.DoubleTimeRelativePairing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem square_pairing (X : TopCat.{0}) (q : ℕ)
    (ψ : RelativeCupCochain.relative (DoubleRelativeTimeCylinder.squarePair X) (q + 2))
    (hψ : RelativeCupCochain.differential (DoubleRelativeTimeCylinder.squarePair X) (q + 2) ψ = 0)
    (c : (chains X).cycles q) :
    RelativeKronecker.comparison (DoubleRelativeTimeCylinder.squarePair X) (q + 2)
      (CochainClass.classOf (RelativeCup.cx (DoubleRelativeTimeCylinder.squarePair X)) (q + 2) ψ hψ)
      ((DoubleRelativeTimeCylinder.homology X q).hom (((chains X).homologyπ q).hom c)) =
    ((chains X).iCycles q ≫ NativeGlobalTimeSquare.squarePrism X q ≫
      RelativeCupCochain.toAmbient (DoubleRelativeTimeCylinder.squarePair X) (q + 2) ψ).hom c := by
  have he := ConcreteCategory.congr_hom (DoubleRelativeTimeCylinder.homologyπ_homology X q) c
  change (DoubleRelativeTimeCylinder.homology X q).hom (((chains X).homologyπ q).hom c) =
    (((DoubleRelativeTimeCylinder.squarePair X).singularChainComplex coeff).homologyπ (q + 2)).hom
      ((DoubleRelativeTimeCylinder.cycles X q).hom c) at he
  have h₀ := congrArg
    (RelativeKronecker.comparison (DoubleRelativeTimeCylinder.squarePair X) (q + 2)
      (CochainClass.classOf (RelativeCup.cx (DoubleRelativeTimeCylinder.squarePair X)) (q + 2) ψ hψ)) he
  have h₁ := RelativeKronecker.comparison_classOf (DoubleRelativeTimeCylinder.squarePair X) (q + 2) ψ hψ
    ((DoubleRelativeTimeCylinder.cycles X q).hom c)
  have hi := ConcreteCategory.congr_hom (DoubleRelativeTimeCylinder.cycles_i X q) c
  change (((DoubleRelativeTimeCylinder.squarePair X).singularChainComplex coeff).iCycles (q + 2)).hom
      ((DoubleRelativeTimeCylinder.cycles X q).hom c) =
    ((chains X).iCycles q ≫ DoubleRelativeTimeCylinder.component X q).hom c at hi
  have hv := congrArg ψ.hom hi
  change _ = (((chains X).iCycles q ≫ DoubleRelativeTimeCylinder.component X q) ≫ ψ).hom c at hv
  have hv' : ψ.hom
      ((((DoubleRelativeTimeCylinder.squarePair X).singularChainComplex coeff).iCycles (q + 2)).hom
        ((DoubleRelativeTimeCylinder.cycles X q).hom c)) =
      ((chains X).iCycles q ≫ NativeGlobalTimeSquare.squarePrism X q ≫
        RelativeCupCochain.toAmbient (DoubleRelativeTimeCylinder.squarePair X) (q + 2) ψ).hom c := by
    have ht := RelativePrismCochainBoundary.toAmbient_eq (DoubleRelativeTimeCylinder.squarePair X) (q + 2) ψ
    have hh := congrArg (fun φ => ((chains X).iCycles q ≫ NativeGlobalTimeSquare.squarePrism X q ≫ φ).hom c) ht
    exact hv.trans (by simpa only [DoubleRelativeTimeCylinder.component,
      NativeGlobalTimeSquare.squarePrism, Category.assoc] using hh)
  exact h₀.trans (h₁.trans hv')

theorem pullback_closed {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (ψ : RelativeCupCochain.relative Q n) (hψ : RelativeCupCochain.differential Q n ψ = 0) :
    RelativeCupCochain.differential P n (RelativeCupCochain.pullback f n ψ) = 0 :=
  CochainClass.closed_map (RelativeCup.cx Q)
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) f) n ψ hψ

theorem pairing (X : TopCat.{0}) (Q : TopPair.{0})
    (f : DoubleRelativeTimeCylinder.squarePair X ⟶ Q) (q : ℕ)
    (ψ : RelativeCupCochain.relative Q (q + 2))
    (hψ : RelativeCupCochain.differential Q (q + 2) ψ = 0) (c : (chains X).cycles q) :
    RelativeKronecker.comparison Q (q + 2)
      (CochainClass.classOf (RelativeCup.cx Q) (q + 2) ψ hψ)
      ((TopPair.singularHomologyMap f coeff (q + 2)).hom
        ((DoubleRelativeTimeCylinder.homology X q).hom (((chains X).homologyπ q).hom c))) =
    ((chains X).iCycles q ≫ NativeGlobalTimeSquare.squarePrism X q ≫
      cochainPullback (TopPair.Hom.fst f) (q + 2) (RelativeCupCochain.toAmbient Q (q + 2) ψ)).hom c := by
  have hc := CochainClass.classOf_map (RelativeCup.cx Q)
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) f)
    (q + 2) ψ hψ (pullback_closed f (q + 2) ψ hψ)
  have hn := congrArg (fun φ => φ
      ((DoubleRelativeTimeCylinder.homology X q).hom (((chains X).homologyπ q).hom c)))
    (RelativeKronecker.naturality f (q + 2) (CochainClass.classOf (RelativeCup.cx Q) (q + 2) ψ hψ))
  have hs := square_pairing X q (RelativeCupCochain.pullback f (q + 2) ψ)
    (pullback_closed f (q + 2) ψ hψ) c
  rw [RelativeCupCochain.toAmbient_pullback] at hs
  exact hn.symm.trans ((congrArg (fun a => RelativeKronecker.comparison
    (DoubleRelativeTimeCylinder.squarePair X) (q + 2) a
      ((DoubleRelativeTimeCylinder.homology X q).hom (((chains X).homologyπ q).hom c))) hc).trans hs)

theorem pairing_zero (X : TopCat.{0}) (Q : TopPair.{0})
    (f : DoubleRelativeTimeCylinder.squarePair X ⟶ Q) (q : ℕ)
    (ψ : RelativeCupCochain.relative Q (q + 2))
    (hψ : RelativeCupCochain.differential Q (q + 2) ψ = 0)
    (hclass : CochainClass.classOf (RelativeCup.cx Q) (q + 2) ψ hψ = 0) (c : (chains X).cycles q) :
    ((chains X).iCycles q ≫ NativeGlobalTimeSquare.squarePrism X q ≫
      cochainPullback (TopPair.Hom.fst f) (q + 2) (RelativeCupCochain.toAmbient Q (q + 2) ψ)).hom c = 0 := by
  have h := pairing X Q f q ψ hψ c
  rw [hclass, map_zero, LinearMap.zero_apply] at h
  exact h.symm

end
end Finsler.DoubleTimeRelativePairing
