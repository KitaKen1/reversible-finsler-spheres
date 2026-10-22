module

public import Finsler.Loop.CanonicalTimeCupBilinear
public import Finsler.Loop.CanonicalTimeCupFilteredPairing
public import Finsler.Topology.KroneckerHomologyExt

/-! One actual global self-cut on cohomology-class input. It is
constructed from the original genuine prism cut, not from a desired
pairing axiom. Actual geometric pairings prove representative/radius
independence and linearity in the tested class. -/
@[expose] public section
namespace Finsler.CanonicalGlobalSelfCut
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def map (m p q : ℕ) (T : cohomologyZMod2 (Loops (m + 1)) p) :
    homologyZMod2 (Loops (m + 1)) ((m + p) + q) ⟶ homologyZMod2 (Loops (m + 1)) q :=
  (PrismSelfCut.operation m p (by norm_num : 0 < (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (classRepr _ p T) (classRepr_isCocycle _ p T)).homology q

theorem pairing (m p q : ℕ) (T : cohomologyZMod2 (Loops (m + 1)) p)
    (B : cohomologyZMod2 (Loops (m + 1)) q)
    (z : homologyZMod2 (Loops (m + 1)) ((m + p) + q)) :
    (kroneckerMap _ q).hom B ((map m p q T).hom z) =
      (kroneckerMap _ ((m + p) + q)).hom (CanonicalGlobalTimeCup.product m p q T B) z := by
  have h := GlobalTimeCupCohomology.pairing m (by norm_num : 0 < (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) p q
    (classRepr _ p T) (classRepr _ q B) (classRepr_isCocycle _ p T) (classRepr_isCocycle _ q B) z
  rw [cocycleClass_classRepr, cocycleClass_classRepr] at h
  exact h.symm

theorem original_prism_eq (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    (PrismSelfCut.operation m p hρ hρr hr T hT).homology q =
      map m p q (cocycleClass _ p T hT) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply KroneckerHomologyExt.homology_ext (Loops (m + 1)) q
  intro B
  obtain ⟨b, hb, rfl⟩ := cocycleClass_surjective (Loops (m + 1)) q B
  exact (GlobalTimeCupCohomology.pairing m hρ hρr hr p q T b hT hb z).symm.trans
    ((congrArg (fun a => (kroneckerMap _ ((m + p) + q)).hom a z)
      (CanonicalGlobalTimeCup.product_compare m hm p q hρ hρr hr _ _)).trans
        (pairing m p q (cocycleClass _ p T hT) (cocycleClass _ q b hb) z).symm)

theorem map_add (m p q : ℕ) (T U : cohomologyZMod2 (Loops (m + 1)) p) :
    map m p q (T + U) = map m p q T + map m p q U := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply KroneckerHomologyExt.homology_ext
  intro B
  simp only [ModuleCat.hom_add, LinearMap.add_apply, _root_.map_add]
  calc
    _ = (kroneckerMap _ ((m + p) + q)).hom (CanonicalGlobalTimeCup.product m p q (T + U) B) z :=
      pairing m p q (T + U) B z
    _ = (kroneckerMap _ ((m + p) + q)).hom (CanonicalGlobalTimeCup.product m p q T B) z +
        (kroneckerMap _ ((m + p) + q)).hom (CanonicalGlobalTimeCup.product m p q U B) z := by
      rw [← CanonicalTimeCupBilinear.bilinear_apply, _root_.map_add, LinearMap.add_apply]
      simp only [_root_.map_add, LinearMap.add_apply, CanonicalTimeCupBilinear.bilinear_apply]
    _ = _ := congrArg₂ (· + ·) (pairing m p q T B z).symm (pairing m p q U B z).symm

theorem map_smul (m p q : ℕ) (c : ZMod 2) (T : cohomologyZMod2 (Loops (m + 1)) p) :
    map m p q (c • T) = c • map m p q T := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply KroneckerHomologyExt.homology_ext
  intro B
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, _root_.map_smul]
  calc
    _ = (kroneckerMap _ ((m + p) + q)).hom (CanonicalGlobalTimeCup.product m p q (c • T) B) z :=
      pairing m p q (c • T) B z
    _ = c • (kroneckerMap _ ((m + p) + q)).hom (CanonicalGlobalTimeCup.product m p q T B) z := by
      rw [← CanonicalTimeCupBilinear.bilinear_apply, _root_.map_smul, LinearMap.smul_apply]
      simp only [_root_.map_smul, LinearMap.smul_apply, CanonicalTimeCupBilinear.bilinear_apply]
    _ = _ := congrArg (c • ·) (pairing m p q T B z).symm

def bilinear (m p q : ℕ) :
    cohomologyZMod2 (Loops (m + 1)) p →ₗ[ZMod 2]
      homologyZMod2 (Loops (m + 1)) ((m + p) + q) →ₗ[ZMod 2] homologyZMod2 (Loops (m + 1)) q where
  toFun T := (map m p q T).hom
  map_add' T U := congrArg ModuleCat.Hom.hom (map_add m p q T U)
  map_smul' c T := congrArg ModuleCat.Hom.hom (map_smul m p q c T)

end
end Finsler.CanonicalGlobalSelfCut
