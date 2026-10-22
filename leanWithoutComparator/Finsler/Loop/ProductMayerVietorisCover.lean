module

public import Finsler.Loop.ProductHomologyZeroDetection

/-! Actual product open covers and their actual Mayer-Vietoris maps.
The overlap identification preserves both genuine projections. -/
@[expose] public section
namespace Finsler.ProductMayerVietorisCover
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def domain {X : TopCat.{0}} (U : Set X) (Y : TopCat.{0}) : Set (product X Y) := Prod.fst ⁻¹' U
abbrev patch {X : TopCat.{0}} (U : Set X) (Y : TopCat.{0}) : TopCat.{0} := TopCat.of (domain U Y)
abbrev overlap {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) : TopCat.{0} :=
  TopCat.of (domain U Y ∩ domain V Y : Set (product X Y))

theorem domain_open {X : TopCat.{0}} {U : Set X} (Y : TopCat.{0}) (hU : IsOpen U) :
    IsOpen (domain U Y) := hU.preimage continuous_fst

theorem domain_cover {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0}) (hUV : U ∪ V = Set.univ) :
    domain U Y ∪ domain V Y = Set.univ := by
  change Prod.fst ⁻¹' U ∪ Prod.fst ⁻¹' V = Set.univ
  rw [← Set.preimage_union, hUV, Set.preimage_univ]

def patchHomeomorph {X : TopCat.{0}} (U : Set X) (Y : TopCat.{0}) :
    patch U Y ≃ₜ product (TopCat.of U) Y where
  toFun p := (⟨p.val.1, p.property⟩, p.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := (continuous_fst.subtype_val.prodMk continuous_snd).subtype_mk _

def overlapHomeomorph {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) :
    overlap U V Y ≃ₜ product (TopCat.of (U ∩ V : Set X)) Y where
  toFun p := (⟨p.val.1, p.property⟩, p.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := (continuous_fst.subtype_val.prodMk continuous_snd).subtype_mk _

def inclusion {X : TopCat.{0}} (U : Set X) (Y : TopCat.{0}) : patch U Y ⟶ product X Y :=
  TopCat.ofHom (ContinuousMap.subtypeVal (domain U Y))
def patchSecond {X : TopCat.{0}} (U : Set X) (Y : TopCat.{0}) : patch U Y ⟶ Y :=
  TopCat.ofHom ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩
def overlapFirst {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) :
    overlap U V Y ⟶ TopCat.of (U ∩ V : Set X) :=
  TopCat.ofHom ⟨fun p => ⟨p.val.1, p.property⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
def overlapSecond {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) : overlap U V Y ⟶ Y :=
  TopCat.ofHom ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩
def north {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) : overlap U V Y ⟶ patch U Y :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)

theorem north_second {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) :
    north U V Y ≫ patchSecond U Y = overlapSecond U V Y := by ext p : 1; rfl
theorem inclusion_second {X : TopCat.{0}} (U : Set X) (Y : TopCat.{0}) :
    inclusion U Y ≫ second X Y = patchSecond U Y := by ext p : 1; rfl
theorem overlap_first_factor {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) :
    (TopCat.isoOfHomeo (overlapHomeomorph U V Y)).hom ≫ first _ Y = overlapFirst U V Y := by
  ext p : 1; rfl
theorem overlap_second_factor {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) :
    (TopCat.isoOfHomeo (overlapHomeomorph U V Y)).hom ≫ second _ Y = overlapSecond U V Y := by
  ext p : 1; rfl

abbrev patches {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) (k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (patch U Y) k ⊞ homologyZMod2 (patch V Y) k
def fromPatches {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) (k : ℕ) :
    patches U V Y k ⟶ homologyZMod2 (product X Y) k :=
  SSet.mayerVietorisFromBiprod coeff (TopCat.toSSet.map (inclusion U Y))
    (TopCat.toSSet.map (inclusion V Y)) k
def toPatches {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) (k : ℕ) :
    homologyZMod2 (overlap U V Y) k ⟶ patches U V Y k :=
  SSet.mayerVietorisToBiprod coeff (TopCat.toSSet.map (north U V Y))
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right))) k

def delta {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ) :
    homologyZMod2 (product X Y) (k + 1) ⟶ homologyZMod2 (overlap U V Y) k :=
  TopCat.mayerVietorisδ (X := product X Y) coeff (domain_open Y hU) (domain_open Y hV)
    (domain_cover Y hUV) (k + 1) k rfl

theorem delta_toPatches {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ) :
    delta Y hU hV hUV k ≫ toPatches U V Y k = 0 :=
  TopCat.mayerVietorisδ_toBiprod (X := product X Y) coeff (domain_open Y hU) (domain_open Y hV)
    (domain_cover Y hUV) (k + 1) k rfl

theorem exact_full {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ) :
    (ShortComplex.mk (fromPatches U V Y (k + 1)) (delta Y hU hV hUV k)
      (TopCat.mayerVietorisFromBiprod_δ (X := product X Y) coeff (domain_open Y hU)
        (domain_open Y hV) (domain_cover Y hUV) (k + 1) k rfl)).Exact :=
  TopCat.mayerVietoris_exact₃ (X := product X Y) coeff (domain_open Y hU) (domain_open Y hV)
    (domain_cover Y hUV) (k + 1) k rfl

theorem first_naturality {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ) :
    delta Y hU hV hUV k ≫ homologyPushZMod2 (overlapFirst U V Y) k =
      homologyPushZMod2 (first X Y) (k + 1) ≫
        TopCat.mayerVietorisδ (X := X) coeff hU hV hUV (k + 1) k rfl :=
  TopCat.mayerVietorisδ_naturality (X := product X Y) (Y := X) coeff
    (domain_open Y hU) (domain_open Y hV) (domain_cover Y hUV) hU hV hUV
    (first X Y) (fun _ h => h) (fun _ h => h) (k + 1) k rfl

end
end Finsler.ProductMayerVietorisCover
