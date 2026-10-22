module

public import Finsler.Loop.MeridianPrimitiveNonzero
public import Finsler.Topology.CrossProjectionZero

/-! Actual based paths, genuine concatenation/cross-product maps,
and the explicit double/triple meridian parameter families. The
primitive is nonzero. Nonzero higher products are NOT assumed. -/
@[expose] public section
namespace Finsler.BasedMeridianProducts
open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev space {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (Path P P)

def forget {n : ℕ} (P : Sphere n) : space P ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun γ => ClosedPathCircle.circle (ClosedPathCircle.ofPath γ),
    ClosedPathCircle.path_circle_continuous P⟩

def concatenate {n : ℕ} (P : Sphere n) : space P ⊗ space P ⟶ space P :=
  TopCat.ofHom ⟨fun z => z.1.trans z.2, Path.continuous_trans⟩

def family {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (equator P) ⟶ space P :=
  TopCat.ofHom ⟨loop P v₀, loop_continuous P v₀⟩

theorem family_forget {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    family P v₀ ≫ forget P = ordinary P v₀ := rfl

def primitive (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (space P) m :=
  (homologyPushZMod2 (family P v₀) m).hom (MeridianEquatorHomology.fundamental m hm P)

theorem forget_primitive (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (homologyPushZMod2 (forget P) m).hom (primitive m hm P v₀) =
      MeridianLoopClass.ordinaryClass m hm P v₀ := by
  have h := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) m).obj coeff).map_comp
      (family P v₀) (forget P)) (MeridianEquatorHomology.fundamental m hm P)
  rw [family_forget] at h
  exact h.symm

theorem primitive_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    primitive m hm P v₀ ≠ 0 := by
  intro hz
  have h := forget_primitive m hm P v₀
  rw [hz, map_zero] at h
  exact MeridianPrimitiveNonzero.ordinary_ne_zero m hm P v₀ h.symm

def product {n : ℕ} (P : Sphere n) (i j k : ℕ) (h : i + j = k) :
    homologyZMod2 (space P) i →ₗ[ZMod 2]
      homologyZMod2 (space P) j →ₗ[ZMod 2] homologyZMod2 (space P) k :=
  (FilteredBilinearLoopProduct.cross (space P) (space P) i j k h).compr₂
    (homologyPushZMod2 (concatenate P) k).hom

def doubleFamily {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  (family P v₀ ⊗ₘ family P v₀) ≫ concatenate P

def tripleFamily {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  (doubleFamily P v₀ ⊗ₘ family P v₀) ≫ concatenate P

def doubleSource (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  FilteredBilinearLoopProduct.cross (TopCat.of (equator P)) (TopCat.of (equator P)) m m (2 * m) (by omega)
    (MeridianEquatorHomology.fundamental m hm P) (MeridianEquatorHomology.fundamental m hm P)

def tripleSource (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  FilteredBilinearLoopProduct.cross (TopCat.of (equator P) ⊗ TopCat.of (equator P)) (TopCat.of (equator P))
    (2 * m) m (3 * m) (by omega) (doubleSource m hm P) (MeridianEquatorHomology.fundamental m hm P)

def square (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  product P m m (2 * m) (by omega) (primitive m hm P v₀) (primitive m hm P v₀)

def cube (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  product P (2 * m) m (3 * m) (by omega) (square m hm P v₀) (primitive m hm P v₀)

theorem doubleFamily_image (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (homologyPushZMod2 (doubleFamily P v₀) (2 * m)).hom (doubleSource m hm P) = square m hm P v₀ := by
  have hn := CrossProjectionZero.cross_naturality_apply (family P v₀) (family P v₀)
    m m (2 * m) (by omega) (MeridianEquatorHomology.fundamental m hm P)
    (MeridianEquatorHomology.fundamental m hm P)
  have hc := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (2 * m)).obj coeff).map_comp
      (family P v₀ ⊗ₘ family P v₀) (concatenate P)) (doubleSource m hm P)
  change _ = (homologyPushZMod2 (concatenate P) (2 * m)).hom _ at hc
  change _ = (homologyPushZMod2 (concatenate P) (2 * m)).hom _
  exact hc.trans (congrArg ((homologyPushZMod2 (concatenate P) (2 * m)).hom) hn.symm)

theorem tripleFamily_image (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (homologyPushZMod2 (tripleFamily P v₀) (3 * m)).hom (tripleSource m hm P) = cube m hm P v₀ := by
  have hn := CrossProjectionZero.cross_naturality_apply (doubleFamily P v₀) (family P v₀)
    (2 * m) m (3 * m) (by omega) (doubleSource m hm P) (MeridianEquatorHomology.fundamental m hm P)
  change FilteredBilinearLoopProduct.cross (space P) (space P) (2 * m) m (3 * m) (by omega)
    ((homologyPushZMod2 (doubleFamily P v₀) (2 * m)).hom (doubleSource m hm P))
    (primitive m hm P v₀) = _ at hn
  rw [doubleFamily_image] at hn
  have hc := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (3 * m)).obj coeff).map_comp
      (doubleFamily P v₀ ⊗ₘ family P v₀) (concatenate P)) (tripleSource m hm P)
  change _ = (homologyPushZMod2 (concatenate P) (3 * m)).hom _ at hc
  change _ = (homologyPushZMod2 (concatenate P) (3 * m)).hom _
  exact hc.trans (congrArg ((homologyPushZMod2 (concatenate P) (3 * m)).hom) hn.symm)

end
end Finsler.BasedMeridianProducts
