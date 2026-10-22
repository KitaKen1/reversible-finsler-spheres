module

public import Finsler.Loop.NormalizedCapRightInterval
public import Finsler.Topology.TimePrismNaturality

/-! The actual canonical right interval is a genuine topological
prism. Its cochain integration retains the source boundary and BOTH
endpoint evaluations. Naturality includes the original coordinate order. -/
@[expose] public section
namespace Finsler.RightIntervalCochain
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

abbrev space (X : TopCat.{0}) := X ⊗ TopCat.I.{0}

def endpoint (X : TopCat.{0}) (t : _root_.unitInterval) : X ⟶ space X :=
  TopCat.ofHom ⟨fun x => (x, ULift.up t), by fun_prop⟩

def cylinder (X : TopCat.{0}) : TopCat.Homotopy (endpoint X 0) (endpoint X 1) where
  toFun z := (z.2, ULift.up z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem cylinder_map (X : TopCat.{0}) : (cylinder X).h = 𝟙 (space X) := rfl

theorem prism (X : TopCat.{0}) (q : ℕ) :
    ((cylinder X).toSSet.chainComplexMap coeff).hom q (q + 1) = TimeTriangleSplit.interval X q := by
  rw [← TimeShuffleComparison.rectangle_eq_prism, TimeShuffleComparison.rectangle, cylinder_map]
  have hi : push (𝟙 (space X)) = 𝟙 (chains (space X)) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (space X))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hi, HomologicalComplex.id_f, Category.comp_id]
  rfl

theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ) :
    (push f).f q ≫ TimeTriangleSplit.interval Y q =
      TimeTriangleSplit.interval X q ≫ (push (f ▷ TopCat.I)).f (q + 1) := by
  rw [← prism, ← prism]
  exact (TimePrismNaturality.prism_pre (cylinder Y) f q).trans
    ((TimePrismNaturality.prism_congr _ _ (by
      change (f ▷ TopCat.I) ≫ (cylinder Y).h = (cylinder X).h ≫ (f ▷ TopCat.I)
      rw [cylinder_map, cylinder_map, Category.comp_id, Category.id_comp]) q).trans
      (TimePrismNaturality.prism_post (cylinder X) (f ▷ TopCat.I) q).symm)

theorem full_boundary (X : TopCat.{0}) (q : ℕ) :
    (push (endpoint X 0)).f (q + 1) =
      (chains X).d (q + 1) q ≫ TimeTriangleSplit.interval X q +
        TimeTriangleSplit.interval X (q + 1) ≫ (chains (space X)).d (q + 2) (q + 1) +
          (push (endpoint X 1)).f (q + 1) := by
  have h := ((cylinder X).toSSet.chainComplexMap coeff).comm (q + 1)
  simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, prism] at h
  exact h

theorem integration_closed (X : TopCat.{0}) (q : ℕ)
    (T : singularCochainGroup (ZMod 2) (space X) (q + 1))
    (hT : cochainCoboundary (ZMod 2) (space X) (q + 1) T = 0)
    (h₀ : cochainPullback (endpoint X 0) (q + 1) T = 0)
    (h₁ : cochainPullback (endpoint X 1) (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) X q (TimeTriangleSplit.interval X q ≫ T) = 0 := by
  have h := congrArg (fun f => f ≫ T) (full_boundary X q)
  have hc : (chains (space X)).d (q + 2) (q + 1) ≫ T = 0 := hT
  have h0 : (push (endpoint X 0)).f (q + 1) ≫ T = 0 := h₀
  have h1 : (push (endpoint X 1)).f (q + 1) ≫ T = 0 := h₁
  simp only [Preadditive.add_comp, Category.assoc, hc, comp_zero, h0, h1, add_zero] at h
  exact h.symm

end
end Finsler.RightIntervalCochain
