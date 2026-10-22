module

public import Finsler.Loop.NativeOriginalBranchValues
public import Finsler.Loop.NativeThetaCoefficientThreeNorth

/-! The ACTUAL northern rotation followed by the ORIGINAL cut-time
prism is the genuine ordinary two-time square prism followed by its
actual cut-parameter map. This is a chain identity in EVERY degree;
no relative lift on the union of square faces is silently assumed. -/
@[expose] public section
namespace Finsler.NativeGlobalTimeSquare
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

abbrev source {n : ℕ} (P : Sphere n) : TopCat.{0} := NativePairDoublePrismSource.source P
abbrev rotationDomain {n : ℕ} (P : Sphere n) := DoubleRelativeTimeCylinder.cylinder (source P)
abbrev squareDomain {n : ℕ} (P : Sphere n) := DoubleRelativeTimeCylinder.cylinder (rotationDomain P)
abbrev northRotation {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : rotationDomain P ⟶ Loops n :=
  NativeFixedReturnRotationZero.quarterFamily P v₀ k 0

def intoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) : squareDomain P ⟶ SelfCutThomCocycle.parameters n :=
  TopCat.ofHom ⟨fun z => (z.1, northRotation P v₀ k z.2),
    continuous_fst.prodMk ((northRotation P v₀ k).hom.continuous.comp continuous_snd)⟩

def squarePrism (X : TopCat.{0}) (q : ℕ) :
    (chains X).X q ⟶ (chains (DoubleRelativeTimeCylinder.cylinder (DoubleRelativeTimeCylinder.cylinder X))).X (q + 2) :=
  ((DoubleRelativeTimeCylinder.homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
    ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder X)).toSSet.chainComplexMap coeff).hom
      (q + 1) (q + 2)

def rawNorth {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : ℕ) :=
  squarePrism (source P) q ≫ (push (intoCut P v₀ k)).f (q + 2)

theorem rotation_prism {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : ℕ) :
    ((DoubleRelativeTimeCylinder.homotopy (source P)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (push (northRotation P v₀ k)).f (q + 1) =
      ((NativeFixedReturnRotationZero.quarterHomotopy P v₀ k 0).toSSet.chainComplexMap coeff).hom q (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (northRotation P v₀ k))
      (DoubleRelativeTimeCylinder.homotopy (source P))).h =
      (NativeFixedReturnRotationZero.quarterHomotopy P v₀ k 0).h := by
    apply TopCat.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_post (DoubleRelativeTimeCylinder.homotopy (source P))
    (northRotation P v₀ k) q).trans (TimePrismNaturality.prism_congr _ _ he q)

theorem cut_prism {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : ℕ) :
    (push (northRotation P v₀ k)).f q ≫ SelfCutTimePrism.prism n q =
      ((DoubleRelativeTimeCylinder.homotopy (rotationDomain P)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        (push (intoCut P v₀ k)).f (q + 1) := by
  have he : ((SelfCutTimePrism.cylinder n).comp (TopCat.Homotopy.refl (northRotation P v₀ k))).h =
      (TopCat.Homotopy.comp (TopCat.Homotopy.refl (intoCut P v₀ k))
        (DoubleRelativeTimeCylinder.homotopy (rotationDomain P))).h := by
    apply TopCat.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_pre (SelfCutTimePrism.cylinder n) (northRotation P v₀ k) q).trans
    ((TimePrismNaturality.prism_congr _ _ he q).trans
      (TimePrismNaturality.prism_post (DoubleRelativeTimeCylinder.homotopy (rotationDomain P)) (intoCut P v₀ k) q).symm)

theorem double_prism {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : ℕ) :
    ((NativeFixedReturnRotationZero.quarterHomotopy P v₀ k 0).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      SelfCutTimePrism.prism n (q + 1) = rawNorth P v₀ k q := by
  rw [← rotation_prism, Category.assoc, cut_prism]
  rfl

theorem intoCut_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (z : squareDomain P) :
    intoCut P v₀ k z = (z.1, SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀ z.2.2)
      (MeridianTripleQuarterClocks.clock k 0 z.2.1)) := rfl

end
end Finsler.NativeGlobalTimeSquare
