module

public import Finsler.Loop.ConstantRelativeOutputPairing
public import Finsler.Topology.CochainClass

/-! Genuine representatives of ALL constant-relative output classes
on the actual H1 loop space. Their original class is retained and
their pullback to the ACTUAL constant-loop subspace is literally zero,
not merely cohomologically zero. -/
@[expose] public section
namespace Finsler.ConstantRelativeOutputCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.BorelLoop Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (n k : ℕ) (a : RelativeCup.cohomology (fullPair n) k)

def representative : RelativeCupCochain.relative (fullPair n) k := CochainClass.representative (RelativeCup.cx (fullPair n)) k a

theorem representative_closed : RelativeCupCochain.differential (fullPair n) k (representative n k a) = 0 :=
  CochainClass.representative_closed (RelativeCup.cx (fullPair n)) k a

def ambient : singularCochainGroup (ZMod 2) (fullPair n).fst k :=
  RelativeCupCochain.toAmbient (fullPair n) k (representative n k a)

theorem ambient_closed : cochainCoboundary (ZMod 2) (fullPair n).fst k (ambient n k a) = 0 :=
  RelativeCup.toAmbient_closed (fullPair n) k _ (representative_closed n k a)

def cochain : singularCochainGroup (ZMod 2) (Loops n) k := cochainPullback (FullLoopModel.insert n) k (ambient n k a)

theorem closed : cochainCoboundary (ZMod 2) (Loops n) k (cochain n k a) = 0 :=
  pullback_closed _ _ _ (ambient_closed n k a)

theorem constants_zero : cochainPullback (SupportedCap.subspaceMap (Loops n) (consts n)) k (cochain n k a) = 0 := by
  have he : SupportedCap.subspaceMap (Loops n) (consts n) ≫ FullLoopModel.insert n = (fullPair n).map := by ext u : 1; rfl
  rw [cochain, ← pullback_comp, he]
  exact RelativeCupCochain.restriction_toAmbient (fullPair n) k (representative n k a)

theorem ambient_class : CochainClass.classOf (cochainCxZMod2 (fullPair n).fst) k (ambient n k a) (ambient_closed n k a) =
    (relativeToPool (fullPair n) k).hom a := by
  have he := RelativeCup.relativeToPool_classOf (fullPair n) k (representative n k a) (representative_closed n k a)
  rw [show CochainClass.classOf (RelativeCup.cx (fullPair n)) k (representative n k a) (representative_closed n k a) = a from
    CochainClass.classOf_representative (RelativeCup.cx (fullPair n)) k a] at he
  exact he.symm

theorem cochain_class : CochainClass.classOf (cochainCxZMod2 (Loops n)) k (cochain n k a) (closed n k a) =
    ConstantRelativeOutputPairing.absolute n k a := by
  have he := CochainClass.classOf_map (cochainCxZMod2 (fullPair n).fst)
    (singularCochainComplexZMod2.map (FullLoopModel.insert n).op) k (ambient n k a) (ambient_closed n k a) (closed n k a)
  change (cohPullback (FullLoopModel.insert n) k).hom
    (CochainClass.classOf (cochainCxZMod2 (fullPair n).fst) k (ambient n k a) (ambient_closed n k a)) =
      CochainClass.classOf (cochainCxZMod2 (Loops n)) k (cochain n k a) (closed n k a) at he
  rw [ambient_class] at he
  exact he.symm

end
end Finsler.ConstantRelativeOutputCochain
