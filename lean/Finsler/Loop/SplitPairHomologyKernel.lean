module

public import Finsler.Loop.ConstantRelativePairing

/-! A genuine retracted topological pair identifies its relative
quotient kernel with the original inclusion image. This uses the REAL
TauCeti long exact sequence, rather than a rank-one premise. -/
@[expose] public section
namespace Finsler.SplitPairHomologyKernel
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem push_comp_apply {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ)
    (z : homologyZMod2 X k) :
    (homologyPushZMod2 g k).hom ((homologyPushZMod2 f k).hom z) =
      (homologyPushZMod2 (f ≫ g) k).hom z :=
  (ConcreteCategory.congr_hom (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).map_comp f g) z).symm

theorem push_id_apply (X : TopCat.{0}) (k : ℕ) (z : homologyZMod2 X k) :
    (homologyPushZMod2 (𝟙 X) k).hom z = z :=
  ConcreteCategory.congr_hom (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).map_id X) z

variable (P : TopPair.{0}) (r : P.fst ⟶ P.snd) (hr : P.map ≫ r = 𝟙 P.snd) (k : ℕ)

include hr in
theorem retract_inclusion (a : homologyZMod2 P.snd k) :
    (homologyPushZMod2 r k).hom ((homologyPushZMod2 P.map k).hom a) = a := by
  rw [push_comp_apply, hr, push_id_apply]

include r hr in
theorem inclusion_injective : Function.Injective (homologyPushZMod2 P.map k).hom := by
  intro a b he
  exact (retract_inclusion P r hr k a).symm.trans
    ((congrArg (homologyPushZMod2 r k).hom he).trans (retract_inclusion P r hr k b))

theorem quotient_inclusion_zero (a : homologyZMod2 P.snd k) :
    (P.singularHomologyπ coeff k).hom ((homologyPushZMod2 P.map k).hom a) = 0 := by
  exact (ConcreteCategory.congr_hom (P.homologyMap_comp_singularHomologyπ coeff k) a).trans rfl

include hr in
theorem quotient_zero_iff (z : homologyZMod2 P.fst k) :
    (P.singularHomologyπ coeff k).hom z = 0 ↔
      z = (homologyPushZMod2 P.map k).hom ((homologyPushZMod2 r k).hom z) := by
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp (P.singularHomology_exact_space coeff k) z hz
    change (homologyPushZMod2 P.map k).hom a = z at ha
    rw [← ha, retract_inclusion P r hr k]
  · intro hz
    rw [hz]
    exact quotient_inclusion_zero P k _

def defect : homologyZMod2 P.fst k →ₗ[ZMod 2] homologyZMod2 P.fst k :=
  LinearMap.id - (homologyPushZMod2 P.map k).hom.comp (homologyPushZMod2 r k).hom

include hr in
theorem retract_defect_zero (z : homologyZMod2 P.fst k) :
    (homologyPushZMod2 r k).hom (defect P r k z) = 0 := by
  change (homologyPushZMod2 r k).hom (z - (homologyPushZMod2 P.map k).hom ((homologyPushZMod2 r k).hom z)) = 0
  rw [map_sub, retract_inclusion P r hr k, sub_self]

theorem quotient_defect (z : homologyZMod2 P.fst k) :
    (P.singularHomologyπ coeff k).hom (defect P r k z) = (P.singularHomologyπ coeff k).hom z := by
  change (P.singularHomologyπ coeff k).hom (z - (homologyPushZMod2 P.map k).hom ((homologyPushZMod2 r k).hom z)) = _
  rw [map_sub, quotient_inclusion_zero, sub_zero]

include hr in
theorem defect_zero_iff (z : homologyZMod2 P.fst k) :
    defect P r k z = 0 ↔ (P.singularHomologyπ coeff k).hom z = 0 := by
  change z - (homologyPushZMod2 P.map k).hom ((homologyPushZMod2 r k).hom z) = 0 ↔ _
  rw [sub_eq_zero, quotient_zero_iff P r hr k z]

include hr in
theorem quotient_injective_on_kernel {x y : homologyZMod2 P.fst k}
    (hx : (homologyPushZMod2 r k).hom x = 0) (hy : (homologyPushZMod2 r k).hom y = 0)
    (hxy : (P.singularHomologyπ coeff k).hom x = (P.singularHomologyπ coeff k).hom y) : x = y := by
  have hz : (P.singularHomologyπ coeff k).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have he := (quotient_zero_iff P r hr k (x - y)).mp hz
  rw [map_sub, hx, hy, sub_self, map_zero] at he
  exact sub_eq_zero.mp he

end
end Finsler.SplitPairHomologyKernel
