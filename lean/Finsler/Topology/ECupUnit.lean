module

public import Finsler.Topology.ECup
public import Finsler.Topology.TrivHq
public import Finsler.Topology.CupUnit

/-! The unit class of H⁰(X, ∅) and the cup with an absolute class in degree zero.

The cochains of an empty space vanish, so the unit cochain of X lifts to a relative cochain of
(X, ∅) (as the pair of univ and univ ∩ ∅); its class is the unit class of H⁰(X, ∅). It is natural
for maps of such pairs and nonzero for a nonempty space, and the map to the absolute cohomology
of univ takes it to the unit class and is linear over cup with absolute classes. Hence the cup
with an absolute class b annihilates no nonzero class of H⁰(X, ∅) if this space has dimension at
most one and the restriction of b to univ is nonzero (`cupInjW_zero`). -/

@[expose] public section

namespace Finsler.ECupUnit

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelComparison Finsler.PairTriple Finsler.TrivHq Finsler.ECup
open Set Module

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The cochains of an empty space vanish. -/
theorem cochain_eq_zero_of_isEmpty {Z : TopCat.{0}} [IsEmpty Z] {p : ℕ}
    (φ : singularCochainGroup (ZMod 2) Z p) : φ = 0 :=
  cochain_ext fun τ => isEmptyElim ((TopCat.toSSetObjEquiv Z _ τ) (Classical.arbitrary _))

/-- Two nonzero vectors of a space of dimension at most one over F₂ are equal. -/
theorem eq_of_ne_zero_dim {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hV : finrank (ZMod 2) V ≤ 1) {x y : V} (hx : x ≠ 0)
    (hy : y ≠ 0) : x = y := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hV
  obtain ⟨c, rfl⟩ := hv x
  obtain ⟨c', rfl⟩ := hv y
  have h2 : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  rcases h2 c with rfl | rfl
  · exact absurd (zero_smul _ v) hx
  rcases h2 c' with rfl | rfl
  · exact absurd (zero_smul _ v) hy
  rfl

variable (X : TopCat.{0})

theorem one_restrict :
    cochainPullback (emptyPair X).map 0 (cochainOne (R := ZMod 2) (Z := (emptyPair X).fst)) = 0 := by
  haveI := isEmpty_snd X
  exact cochain_eq_zero_of_isEmpty _

/-- The relative unit cochain of (X, ∅). -/
def unitCochain : RelativeCupCochain.relative (emptyPair X) 0 :=
  Classical.choose (RelativeCupCochain.exists_lift (emptyPair X) 0 _ (one_restrict X))

theorem toAmbient_unit :
    RelativeCupCochain.toAmbient (emptyPair X) 0 (unitCochain X) =
      cochainOne (R := ZMod 2) (Z := (emptyPair X).fst) :=
  Classical.choose_spec (RelativeCupCochain.exists_lift (emptyPair X) 0 _ (one_restrict X))

theorem unit_closed : RelativeCupCochain.differential (emptyPair X) 0 (unitCochain X) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (emptyPair X) (0 + 1)
  rw [RelativeCupCochain.toAmbient_differential, toAmbient_unit, map_zero]
  exact cochainCoboundary_cochainOne _

/-- **The unit class of H⁰(X, ∅).** -/
def unitH : H (triv (emptyPair X)) 0 :=
  Submodule.Quotient.mk ⟨unitCochain X, unit_closed X⟩

/-- The unit class is nonzero for a nonempty space. -/
theorem unitH_ne_zero (x : X) : unitH X ≠ 0 := by
  intro h
  rw [unitH, Submodule.Quotient.mk_eq_zero] at h
  have h0 : unitCochain X = 0 := (Submodule.mem_bot (ZMod 2)).mp h
  have h1 := toAmbient_unit X
  rw [h0, map_zero] at h1
  let σ : singularSimplices (emptyPair X).fst 0 :=
    (TopCat.toSSetObjEquiv (emptyPair X).fst _).symm
      (ContinuousMap.const _ (⟨x, mem_univ x⟩ : (univ : Set X)))
  have h2 := congrArg (fun φ => cochainEval 0 φ σ) h1
  simp only [cochainOne_eval] at h2
  exact zero_ne_one h2

/-- The unit class is natural. -/
theorem unitH_natural {Y : TopCat.{0}} (f : emptyPair X ⟶ emptyPair Y) :
    Hmap (trivHom f) 0 (unitH Y) = unitH X := by
  rw [unitH, unitH, Hmap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change RelativeCupCochain.pullback f 0 (unitCochain Y) = unitCochain X
  apply RelativeCupCochain.toAmbient_injective (emptyPair X) 0
  rw [RelativeCupCochain.toAmbient_pullback, toAmbient_unit, toAmbient_unit]
  apply cochain_ext
  intro σ
  rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]

/-- The map from the cohomology of (X, ∅) to the absolute cohomology of univ. -/
def toAbs (q : ℕ) : H (triv (emptyPair X)) q →ₗ[ZMod 2] cohomologyZMod2 (emptyPair X).fst q :=
  (Finsler.CochainComparison.relativeToPool (emptyPair X) q).hom ∘ₗ
    (ordinaryEquiv (emptyPair X) (𝟙 _) (Category.comp_id _) q).toLinearMap

theorem toAbs_cupH {p : ℕ} (a : cohomologyZMod2 (emptyPair X).fst p) (q : ℕ)
    (x : H (triv (emptyPair X)) q) :
    toAbs X (p + q) (cupH (emptyPair X) a q x) = cupZMod2 a (toAbs X q x) := by
  simp only [toAbs, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cupH, ordinaryCup_native, Finsler.RelativeCup.relativeToPool_cup]

theorem toAbs_unit : toAbs X 0 (unitH X) = oneZMod2 (emptyPair X).fst := by
  simp only [toAbs, LinearMap.comp_apply, LinearEquiv.coe_coe, unitH]
  rw [ordinaryEquiv_mk, Finsler.RelativeCup.relativeToPool_classOf]
  exact CochainClass.classOf_congr _ 0 (toAmbient_unit X) _ _

/-- The cup of the unit class with an absolute class is that class. -/
theorem toAbs_cup_unit {p : ℕ} (a : cohomologyZMod2 (emptyPair X).fst p) :
    toAbs X (p + 0) (cupH (emptyPair X) a 0 (unitH X)) = a := by
  rw [toAbs_cupH, toAbs_unit]
  exact Finsler.CupUnit.absolute_one_right _ p a

/-- The restriction of a nonzero class to univ is nonzero. -/
theorem res_univ_ne_zero {p : ℕ} {b : cohomologyZMod2 X p} (hb : b ≠ 0) :
    res b (univ : Set X) ≠ 0 := by
  let ψ : X ⟶ TopCat.of ↥(univ : Set X) :=
    TopCat.ofHom ⟨fun x => ⟨x, mem_univ x⟩, continuous_id.subtype_mk _⟩
  have hψ : ψ ≫ incl (univ : Set X) = 𝟙 X := rfl
  intro h
  apply hb
  have e := Finsler.Cup.pullback_comp ψ (incl (univ : Set X)) p b
  rw [hψ, Finsler.DiagonalCohomology.pullback_id] at e
  rw [e]
  unfold res at h
  rw [h, map_zero]

/-- **The cup with an absolute class on H⁰(X, ∅).** If H⁰(X, ∅) has dimension at most one and
the restriction of b to univ is nonzero, the cup with b annihilates no nonzero class of degree 0. -/
theorem cupInjW_zero {p : ℕ} (b : cohomologyZMod2 X p) (x₀ : X)
    [Module.Finite (ZMod 2) (H (triv (emptyPair X)) 0)]
    (hdim : finrank (ZMod 2) (H (triv (emptyPair X)) 0) ≤ 1) (hb : res b (univ : Set X) ≠ 0) :
    CupInjW b (inter_subset_left : (univ : Set X) ∩ ∅ ⊆ univ) 0 := by
  intro x hx h0
  have he := eq_of_ne_zero_dim hdim hx (unitH_ne_zero X x₀)
  rw [he] at h0
  apply hb
  have h1 := toAbs_cup_unit X (res b (univ : Set X))
  rw [h0, map_zero] at h1
  exact h1.symm

end

end Finsler.ECupUnit
