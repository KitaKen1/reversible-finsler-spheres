module

public import Finsler.Loop.SphereProductHomologyDetection

/-! Actual vanishing inputs for the shifted sphere-product induction.
In particular the disconnected zero-sphere base case uses actual
Mayer-Vietoris exactness, rather than connected-base factorization. -/
@[expose] public section
namespace Finsler.ProductMayerVietorisVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductMayerVietorisCover
open scoped ContinuousMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem patch_zero {X : TopCat.{0}} (U : Set X) [ContractibleSpace U] (Y : TopCat.{0}) (k : ℕ)
    (hY : IsZero (homologyZMod2 Y k)) : IsZero (homologyZMod2 (patch U Y) k) :=
  hY.of_iso (((patchHomeomorph U Y).toHomotopyEquiv.trans
    (contractibleProductEquiv (TopCat.of U) Y)).singularHomologyIso coeff k)

theorem empty_zero (X : TopCat.{0}) [IsEmpty X] : IsZero (homologyZMod2 X 0) := by
  have : IsEmpty (ZerothHomotopy X) :=
    ⟨fun c => ZerothHomotopy.rec (motive := fun _ => False) (fun x => isEmptyElim x) c⟩
  exact ((IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun c => isEmptyElim c)).of_iso
    (X.singularHomology₀Iso coeff)

theorem zero_of_patch_and_overlap {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ)
    (hu : IsZero (homologyZMod2 (patch U Y) (k + 1)))
    (hv : IsZero (homologyZMod2 (patch V Y) (k + 1)))
    (ho : IsZero (homologyZMod2 (overlap U V Y) k)) :
    IsZero (homologyZMod2 (product X Y) (k + 1)) := by
  have hf : fromPatches U V Y (k + 1) = 0 := by
    apply biprod.hom_ext'
    · exact hu.eq_of_src _ _
    · exact hv.eq_of_src _ _
  have hs := ModuleCat.subsingleton_of_isZero ho
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => ?_⟩
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_full Y hU hV hUV k)
    (a - b) (hs.elim _ _)
  change (fromPatches U V Y (k + 1)).hom c = a - b at hc
  rw [hf, ModuleCat.hom_zero, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc.symm

end
end Finsler.ProductMayerVietorisVanishing
