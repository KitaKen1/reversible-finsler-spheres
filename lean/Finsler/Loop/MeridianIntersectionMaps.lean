module

public import Finsler.Loop.MeridianCoverPrisms
public import Finsler.Loop.MeridianEquatorHomology
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-! The actual varying/fixed equator maps into the antipodal
intersection. The varying map is a genuine homotopy equivalence;
the fixed map vanishes on positive homology. These identify the
two terms of the actual cover-prism boundary. -/

@[expose] public section
namespace Finsler.MeridianIntersectionMaps
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Topology
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily Finsler.MeridianQuarterHomotopies
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1400000

def reorder {n : ℕ} (P : Sphere n) :
    ({P}ᶜ ∩ {-P}ᶜ : Set (BorelEvaluation.sphere n)) ≃ₜ (upper P ∩ lower P : Set (BorelEvaluation.sphere n)) :=
  Homeomorph.setCongr (by
    have ha : antipode P = -P := rfl
    rw [upper, lower, ha, Set.inter_comm])

def homotopyEquiv {n : ℕ} (P : Sphere n) :
    ContinuousMap.HomotopyEquiv (equator P) ↥(upper P ∩ lower P) :=
  (MeridianEquatorHomology.homeomorph P).toHomotopyEquiv.trans
    ((TauCeti.equatorHomotopyEquiv P).symm.trans (reorder P).toHomotopyEquiv)

theorem homotopyEquiv_value {n : ℕ} (P : Sphere n) (v : equator P) :
    (homotopyEquiv P v).val = v.val := by
  apply Subtype.ext
  change (((TauCeti.equatorHomotopyEquiv P).symm
    (MeridianEquatorHomology.toOrthogonal P v) : Sphere n) : Ambient n) = (v.val : Ambient n)
  rw [TauCeti.coe_equatorHomotopyEquiv_symm_apply]
  rfl

def varying {n : ℕ} (P : Sphere n) : parameters P ⟶ TopCat.of ↥(upper P ∩ lower P) :=
  TopCat.ofHom (homotopyEquiv P).toFun

def fixed {n : ℕ} (P : Sphere n) (v₀ : equator P) : parameters P ⟶ TopCat.of ↥(upper P ∩ lower P) :=
  TopCat.ofHom (ContinuousMap.const (equator P) (homotopyEquiv P v₀))

def intoUpper {n : ℕ} (P : Sphere n) : TopCat.of ↥(upper P ∩ lower P) ⟶ TopCat.of (upper P) :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)

def intoLower {n : ℕ} (P : Sphere n) : TopCat.of ↥(upper P ∩ lower P) ⟶ TopCat.of (lower P) :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right)

theorem upper_fixed {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    HomotopyRangeRestriction.start (returnOutgoingH P v₀) (upper P) (returnOutgoing_upper P v₀) =
      fixed P v₀ ≫ intoUpper P := by
  ext v : 1
  apply Subtype.ext
  exact (homotopyEquiv_value P v₀).symm

theorem upper_varying {n : ℕ} (P : Sphere n) :
    HomotopyRangeRestriction.finish (outgoingH P) (upper P) (outgoing_upper P) =
      varying P ≫ intoUpper P := by
  ext v : 1
  apply Subtype.ext
  exact (homotopyEquiv_value P v).symm

theorem lower_varying {n : ℕ} (P : Sphere n) :
    HomotopyRangeRestriction.start (incomingH P) (lower P) (incoming_lower P) =
      varying P ≫ intoLower P := by
  ext v : 1
  apply Subtype.ext
  exact (homotopyEquiv_value P v).symm

theorem lower_fixed {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    HomotopyRangeRestriction.finish (returnIncomingH P v₀) (lower P) (returnIncoming_lower P v₀) =
      fixed P v₀ ≫ intoLower P := by
  ext v : 1
  apply Subtype.ext
  exact (homotopyEquiv_value P v₀).symm

theorem varying_homology_injective {n : ℕ} (P : Sphere n) (q : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap (push (varying P)) q).hom := by
  have hi := ((homotopyEquiv P).singularHomologyIso coeff q).toLinearEquiv.injective
  change Function.Injective (((homotopyEquiv P).singularHomologyIso coeff q).hom).hom at hi
  rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom] at hi
  exact hi

theorem fixed_homology_zero {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) (hq : q ≠ 0) :
    HomologicalComplex.homologyMap (push (fixed P v₀)) q = 0 := by
  let pt : TopCat.{0} := TopCat.of PUnit
  let a : parameters P ⟶ pt := TopCat.ofHom (ContinuousMap.const (equator P) PUnit.unit)
  let b : pt ⟶ TopCat.of ↥(upper P ∩ lower P) :=
    TopCat.ofHom (ContinuousMap.const PUnit (homotopyEquiv P v₀))
  have hf : fixed P v₀ = a ≫ b := by ext v : 1; rfl
  have hz : IsZero ((chains pt).homology q) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (C := ModuleCat.{0} (ZMod 2)) (n := q) coeff pt hq
  rw [hf, push_comp, HomologicalComplex.homologyMap_comp]
  have ha : HomologicalComplex.homologyMap (push a) q = 0 := hz.eq_of_tgt _ _
  rw [ha, zero_comp]

end
end Finsler.MeridianIntersectionMaps
