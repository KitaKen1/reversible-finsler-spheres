module

public import Finsler.Loop.NativeEvaluationProductDetection
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-! The degree-zero base case for projection detection on a sphere
product. The second factor is genuinely path connected; no continuously
chosen family of paths and no Kunneth isomorphism is assumed. -/
@[expose] public section
namespace Finsler.ProductHomologyZeroDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

abbrev product (X Y : TopCat.{0}) : TopCat.{0} := TopCat.of (X × Y)

def first (X Y : TopCat.{0}) : product X Y ⟶ X := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
def second (X Y : TopCat.{0}) : product X Y ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
def pointSection (X Y : TopCat.{0}) (y : Y) : X ⟶ product X Y :=
  TopCat.ofHom ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩

def Detects (X Y : TopCat.{0}) (k : ℕ) : Prop :=
  ∀ z : homologyZMod2 (product X Y) k,
    (homologyPushZMod2 (first X Y) k).hom z = 0 →
    (homologyPushZMod2 (second X Y) k).hom z = 0 → z = 0

theorem point_sections_equal_of_joined {X : TopCat.{0}} {x y : X} (h : Joined x y) :
    TauCeti.singularHomology₀Section coeff x = TauCeti.singularHomology₀Section coeff y := by
  apply (cancel_mono (X.singularHomology₀Iso coeff).hom).mp
  rw [TauCeti.singularHomology₀Section_singularHomology₀Iso_hom,
    TauCeti.singularHomology₀Section_singularHomology₀Iso_hom]
  obtain ⟨p⟩ := h
  rw [ZerothHomotopy.sound p]

theorem homology_zero_hom_ext {X : TopCat.{0}} {M : ModuleCat.{0} (ZMod 2)}
    (f g : homologyZMod2 X 0 ⟶ M)
    (h : ∀ x : X, TauCeti.singularHomology₀Section coeff x ≫ f =
      TauCeti.singularHomology₀Section coeff x ≫ g) : f = g := by
  apply (cancel_epi (X.singularHomology₀Iso coeff).inv).mp
  apply Sigma.hom_ext
  intro c
  induction c using ZerothHomotopy.rec with
  | mk x =>
    have hi : Sigma.ι (fun _ : ZerothHomotopy X => coeff) (ZerothHomotopy.mk x) ≫
        (X.singularHomology₀Iso coeff).inv = TauCeti.singularHomology₀Section coeff x := by
      rw [← TauCeti.singularHomology₀Section_singularHomology₀Iso_hom]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [← Category.assoc, hi] using h x

theorem first_section (X Y : TopCat.{0}) (y : Y) : pointSection X Y y ≫ first X Y = 𝟙 X := by
  ext x : 1
  rfl

theorem point_section_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    TauCeti.singularHomology₀Section coeff x ≫ homologyPushZMod2 f 0 =
      TauCeti.singularHomology₀Section coeff (f x) :=
  TauCeti.singularHomology₀Section_naturality coeff f x

theorem first_zero_left_inverse (X Y : TopCat.{0}) [PathConnectedSpace Y] (y : Y) :
    homologyPushZMod2 (first X Y) 0 ≫ homologyPushZMod2 (pointSection X Y y) 0 =
      𝟙 (homologyZMod2 (product X Y) 0) := by
  apply homology_zero_hom_ext
  intro p
  have hi : TauCeti.singularHomology₀Section coeff p ≫
      𝟙 (homologyZMod2 (product X Y) 0) = TauCeti.singularHomology₀Section coeff p :=
    Category.comp_id _
  rw [hi]
  rw [← Category.assoc, point_section_naturality,
    point_section_naturality]
  exact point_sections_equal_of_joined
    ((Joined.refl p.1).prod (PathConnectedSpace.joined y p.2))

theorem first_zero_injective (X Y : TopCat.{0}) [PathConnectedSpace Y] :
    Function.Injective (homologyPushZMod2 (first X Y) 0).hom := by
  obtain ⟨y⟩ := PathConnectedSpace.nonempty (X := Y)
  intro a b hab
  have ha := ConcreteCategory.congr_hom (first_zero_left_inverse X Y y) a
  have hb := ConcreteCategory.congr_hom (first_zero_left_inverse X Y y) b
  change (homologyPushZMod2 (pointSection X Y y) 0).hom
    ((homologyPushZMod2 (first X Y) 0).hom a) = a at ha
  change (homologyPushZMod2 (pointSection X Y y) 0).hom
    ((homologyPushZMod2 (first X Y) 0).hom b) = b at hb
  exact ha.symm.trans ((congrArg _ hab).trans hb)

theorem detects_zero (X Y : TopCat.{0}) [PathConnectedSpace Y] : Detects X Y 0 := by
  intro z hz _
  exact first_zero_injective X Y (hz.trans (map_zero _).symm)

end
end Finsler.ProductHomologyZeroDetection
