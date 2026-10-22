module

public import Finsler.Loop.NativeFilteredThetaDetection
public import Finsler.Loop.NativeThetaRelativeDetection
public import Finsler.Loop.SplitPairHomologyKernel

/-! The ORIGINAL Theta survives constants already in its ACTUAL
finite strict-length pair for EVERY reversible metric. Its image is
the same detected original full relative class. The true quotient
maps and pair inclusions are compared, with no independent rank input. -/
@[expose] public section
namespace Finsler.NativeFilteredRelativeTheta
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.StrictLengthEnergyBridge Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def constants {n : ℕ} (F : ReversibleMetric n) (A : ℝ) : Set (lengthSpace F A) := {u | u.val ∈ consts n}
abbrev pair {n : ℕ} (F : ReversibleMetric n) (A : ℝ) : TopPair.{0} := TopPair.ofSubset (constants F A)

def constantsMap {n : ℕ} (F : ReversibleMetric n) (A : ℝ) : (pair F A).snd ⟶ (fullPair n).snd :=
  TopCat.ofHom ⟨fun u => ⟨u.val.val, u.property⟩, continuous_subtype_val.subtype_val.subtype_mk _⟩

def pairMap {n : ℕ} (F : ReversibleMetric n) (A : ℝ) : pair F A ⟶ fullPair n :=
  TopPair.ofHom (LengthFilteredLoopRotation.full F A ≫ FullLoopModel.insert n) (constantsMap F A) (by ext u : 1; rfl)

theorem quotient_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (k : ℕ) (z : homologyZMod2 P.fst k) :
    (Q.singularHomologyπ coeff k).hom ((homologyPushZMod2 (TopPair.Hom.fst f) k).hom z) =
      (P.singularHomologyMap f coeff k).hom ((P.singularHomologyπ coeff k).hom z) := by
  have he := congrArg (fun c => HomologicalComplex.homologyMap c k) (TopPair.singularChainComplexπ_pair_naturality f coeff)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact ConcreteCategory.congr_hom he z

variable (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P)

def input : ((pair F (NativeThetaLengthCut.bound F P v₀)).singularHomology coeff ((m + m) + (m + 1)) : ModuleCat.{0} (ZMod 2)) :=
  ((pair F (NativeThetaLengthCut.bound F P v₀)).singularHomologyπ coeff ((m + m) + (m + 1))).hom (NativeThetaLengthCut.input m hm F P v₀)

theorem input_full :
    ((pair F (NativeThetaLengthCut.bound F P v₀)).singularHomologyMap (pairMap F (NativeThetaLengthCut.bound F P v₀))
      coeff ((m + m) + (m + 1))).hom (input m hm F P v₀) = NativeThetaRelativeDetection.input m hm P v₀ := by
  have he := quotient_natural (pairMap F (NativeThetaLengthCut.bound F P v₀)) ((m + m) + (m + 1)) (NativeThetaLengthCut.input m hm F P v₀)
  have hf : (homologyPushZMod2 (TopPair.Hom.fst (pairMap F (NativeThetaLengthCut.bound F P v₀))) ((m + m) + (m + 1))).hom
      (NativeThetaLengthCut.input m hm F P v₀) =
      (homologyPushZMod2 (FullLoopModel.insert (m + 1)) ((m + m) + (m + 1))).hom (MeridianThetaCutCoefficient.thetaInput m hm P v₀) := by
    change (homologyPushZMod2 (LengthFilteredLoopRotation.full F (NativeThetaLengthCut.bound F P v₀) ≫ FullLoopModel.insert (m + 1)) ((m + m) + (m + 1))).hom _ = _
    rw [← SplitPairHomologyKernel.push_comp_apply, NativeThetaLengthCut.input_full]
  rw [hf] at he
  exact he.symm

theorem input_ne_zero : input m hm F P v₀ ≠ 0 := by
  intro hz
  have he := input_full m hm F P v₀
  rw [hz, map_zero] at he
  exact NativeThetaRelativeDetection.input_ne_zero m hm P v₀ he.symm

end
end Finsler.NativeFilteredRelativeTheta
