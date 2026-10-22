module

public import Finsler.Topology.SingularNormalization
public import Finsler.Topology.RelativeCup

/-! A class vanishing on an actual subspace has an actual closed normalized
cochain representative vanishing there literally, in the pinned singular model. -/

@[expose] public section
namespace Finsler.NormalizedRelativeRepresentative

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison
open scoped DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) (A : Set X) (p : ℕ) (a : cohomologyZMod2 X p)
  (ha : (cohPullback (SupportedCap.subspaceMap X A) p).hom a = 0)

def pair : TopPair.{0} := TopPair.ofSubset A

def relativeClass : (pair X A).singularCohomology coeff (ZMod 2) coeff p :=
  (CochainComparison.relative_lift (pair X A) p a ha).choose

theorem relativeClass_image : (relativeToPool (pair X A) p).hom (relativeClass X A p a ha) = a := by
  have h := (CochainComparison.relative_lift (pair X A) p a ha).choose_spec
  change (cohomologyEquiv X p).symm
    (((pair X A).singularCohomologyπ coeff (ZMod 2) coeff p).hom (relativeClass X A p a ha)) = a
  exact (congrArg (cohomologyEquiv X p).symm h).trans
    ((cohomologyEquiv X p).symm_apply_apply a)

def relativeCocycle : RelativeCupCochain.relative (pair X A) p :=
  CochainClass.representative (RelativeCup.cx (pair X A)) p (relativeClass X A p a ha)

theorem relative_closed :
    RelativeCupCochain.differential (pair X A) p (relativeCocycle X A p a ha) = 0 :=
  CochainClass.representative_closed (RelativeCup.cx (pair X A)) p (relativeClass X A p a ha)

def raw : singularCochainGroup (ZMod 2) X p :=
  RelativeCupCochain.toAmbient (pair X A) p (relativeCocycle X A p a ha)

theorem raw_closed : cochainCoboundary (ZMod 2) X p (raw X A p a ha) = 0 :=
  RelativeCup.toAmbient_closed (pair X A) p (relativeCocycle X A p a ha) (relative_closed X A p a ha)

theorem raw_supported : cochainPullback (SupportedCap.subspaceMap X A) p (raw X A p a ha) = 0 :=
  RelativeCupCochain.restriction_toAmbient (pair X A) p (relativeCocycle X A p a ha)

theorem raw_class : CochainClass.classOf (cochainCxZMod2 X) p (raw X A p a ha)
    (raw_closed X A p a ha) = a := by
  have hc := CochainClass.classOf_representative (RelativeCup.cx (pair X A)) p
    (relativeClass X A p a ha)
  calc
    _ = (relativeToPool (pair X A) p).hom
        (CochainClass.classOf (RelativeCup.cx (pair X A)) p (relativeCocycle X A p a ha)
          (relative_closed X A p a ha)) :=
      (RelativeCup.relativeToPool_classOf (pair X A) p (relativeCocycle X A p a ha)
        (relative_closed X A p a ha)).symm
    _ = _ := (congrArg (relativeToPool (pair X A) p).hom hc).trans (relativeClass_image X A p a ha)

def cocycle : singularCochainGroup (ZMod 2) X p :=
  SingularNormalization.normalize X p (raw X A p a ha)

theorem cocycle_closed : cochainCoboundary (ZMod 2) X p (cocycle X A p a ha) = 0 :=
  SingularNormalization.normalize_closed X p (raw X A p a ha) (raw_closed X A p a ha)

theorem cocycle_supported : cochainPullback (SupportedCap.subspaceMap X A) p (cocycle X A p a ha) = 0 :=
  SingularNormalization.normalize_supported (SupportedCap.subspaceMap X A) p (raw X A p a ha)
    (raw_supported X A p a ha)

theorem cocycle_normalized :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) (cocycle X A p a ha) :=
  SingularNormalization.normalize_degeneracies X p (raw X A p a ha)

theorem cocycle_class (hp : 1 ≤ p) : CochainClass.classOf (cochainCxZMod2 X) p
    (cocycle X A p a ha) (cocycle_closed X A p a ha) = a := by
  exact (SingularNormalization.normalize_class_pos X p hp (raw X A p a ha)
    (raw_closed X A p a ha)).trans (raw_class X A p a ha)

end
end Finsler.NormalizedRelativeRepresentative
