module

public import Finsler.Topology.PoolCupComparison

/-! The actual singular cap product with the project's F₂ cohomology model.
The projection formula and cap--cup associativity have no comparison hypotheses. -/

@[expose] public section

namespace Finsler.PoolCap

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev homology (X : TopCat.{0}) (q : ℕ) : ModuleCat.{0} (ZMod 2) :=
  ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).obj X

abbrev push {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ) : homology X q ⟶ homology Y q :=
  ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).map f

def cap (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 X p) : homology X n →ₗ[ZMod 2] homology X q :=
  (X.singularCap (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
    (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q n h (cohomologyEquiv X p a)).hom

theorem add_left (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a b : cohomologyZMod2 X p) (x : homology X n) :
    cap X p q n h (a + b) x = cap X p q n h a x + cap X p q n h b x := by
  simp only [cap, map_add, ModuleCat.hom_add]
  rfl

theorem smul_left (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (c : ZMod 2) (a : cohomologyZMod2 X p) (x : homology X n) :
    cap X p q n h (c • a) x = c • cap X p q n h a x := by
  simp only [cap, map_smul, ModuleCat.hom_smul]
  rfl

theorem zero_left (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n) (x : homology X n) :
    cap X p q n h 0 x = 0 := by
  simp only [cap, map_zero, ModuleCat.hom_zero]
  rfl

theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 Y p) (x : homology X n) :
    (push f q).hom (cap X p q n h ((cohPullback f p).hom a) x) =
      cap Y p q n h a ((push f n).hom x) := by
  unfold cap
  refine (congrArg (fun z => (push f q).hom
    ((X.singularCap (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q n h z).hom x))
    (cohomology_natural_apply f p a)).trans ?_
  exact ConcreteCategory.congr_hom
    (TopCat.singularCap_naturality f (ZMod 2)
      (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
      p q n h (cohomologyEquiv Y p a)) x

theorem assoc (X : TopCat.{0}) {p q r m n : ℕ} (hp : p + m = n) (hq : q + r = m)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) (x : homology X n) :
    cap X q r m hq b (cap X p m n hp a x) =
      cap X (p + q) r n (by omega) (cupZMod2 a b) x := by
  unfold cap
  rw [Finsler.PoolCupComparison.cohomology_comparison]
  exact ConcreteCategory.congr_hom
    (TopCat.singularCap_assoc X (ZMod 2) hp hq
      (cohomologyEquiv X p a) (cohomologyEquiv X q b)) x

/-- A class whose pullback vanishes caps to zero on every homology class
represented by the image of that map. -/
theorem zero_on_image {X Y : TopCat.{0}} (f : X ⟶ Y) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 Y p) (ha : (cohPullback f p).hom a = 0)
    (x : homology X n) : cap Y p q n h a ((push f n).hom x) = 0 := by
  rw [← naturality f p q n h a x, ha, zero_left, map_zero]

end

end Finsler.PoolCap
