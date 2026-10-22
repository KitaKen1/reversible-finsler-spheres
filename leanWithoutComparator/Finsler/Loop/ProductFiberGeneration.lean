module

public import Finsler.Loop.SphereProductFirstDegreeDetection
public import Finsler.Loop.SphereProductShiftedDetection

/-! The actual second-projection injectivity transports through a
base homotopy equivalence and makes the actual fixed fiber generate
the entire product homology group. -/
@[expose] public section
namespace Finsler.ProductFiberGeneration
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection Finsler.ProductHomologyDetectionTransport
open scoped ContinuousMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem second_injective_of_equiv {X X' : TopCat.{0}} (e : X ≃ₕ X') (Y : TopCat.{0}) (k : ℕ)
    (hi : Function.Injective (homologyPushZMod2 (second X' Y) k).hom) :
    Function.Injective (homologyPushZMod2 (second X Y) k).hom := by
  let f : X ⟶ X' := TopCat.ofHom e.toFun
  let eH := (productEquiv e Y).singularHomologyIso coeff k
  have heH : eH.hom = homologyPushZMod2 (mapFirst f Y) k :=
    (productEquiv e Y).singularHomologyIso_hom coeff k
  intro a b hab
  apply eH.toLinearEquiv.injective
  apply hi
  change (homologyPushZMod2 (second X' Y) k).hom (eH.hom.hom a) =
    (homologyPushZMod2 (second X' Y) k).hom (eH.hom.hom b)
  rw [heH]
  change (homologyPushZMod2 (second X' Y) k).hom ((homologyPushZMod2 (mapFirst f Y) k).hom a) =
    (homologyPushZMod2 (second X' Y) k).hom ((homologyPushZMod2 (mapFirst f Y) k).hom b)
  rw [SplitPairHomologyKernel.push_comp_apply, SplitPairHomologyKernel.push_comp_apply,
    mapFirst_second]
  exact hab

theorem fiber_surjective {X Y : TopCat.{0}} (k : ℕ) (x : X)
    (hi : Function.Injective (homologyPushZMod2 (second X Y) k).hom) :
    Function.Surjective (homologyPushZMod2 (fiberSection X Y x) k).hom := by
  intro z
  refine ⟨(homologyPushZMod2 (second X Y) k).hom z, ?_⟩
  apply hi
  rw [SplitPairHomologyKernel.push_comp_apply, fiberSection_second, SplitPairHomologyKernel.push_id_apply]

end
end Finsler.ProductFiberGeneration
