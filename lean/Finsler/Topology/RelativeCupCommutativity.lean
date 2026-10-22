module

public import Finsler.Topology.RelativeCupOne
public import Finsler.Topology.CupIteration

/-! The actual left and right mixed relative cup classes coincide, including degree zero. -/

@[expose] public section

namespace Finsler.RelativeCupCommutativity

open CategoryTheory Simplicial SphereOddDegree Finsler.CochainComparison
open SphereOddDegree.AlexanderWhitney Finsler.RelativeCupCochain

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem classOf_eq_of_boundary {R : Type} [Ring R]
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (i n : ℕ) (η : C.X i) (φ ψ : C.X n)
    (hφ : (C.d n (n + 1)).hom φ = 0) (hψ : (C.d n (n + 1)).hom ψ = 0)
    (h : φ - ψ = (C.d i n).hom η) :
    CochainClass.classOf C n φ hφ = CochainClass.classOf C n ψ hψ := by
  let u := C.cyclesMk φ (n + 1) (CochainClass.next_eq n) hφ
  let v := C.cyclesMk ψ (n + 1) (CochainClass.next_eq n) hψ
  have hc : u - v = (C.toCycles i n).hom η := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    rw [map_sub]
    have hu : (C.iCycles n).hom u = φ := C.i_cyclesMk _ _ _ _
    have hv : (C.iCycles n).hom v = ψ := C.i_cyclesMk _ _ _ _
    rw [hu, hv]
    exact h.trans (ConcreteCategory.congr_hom (C.toCycles_i i n) η).symm
  have hh := congrArg (C.homologyπ n).hom hc
  rw [map_sub] at hh
  exact sub_eq_zero.mp (hh.trans (ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ i n) η))

theorem absolute_cochain_zero_comm (X : TopCat.{0})
    (φ ψ : singularCochainGroup (ZMod 2) X 0) : cochainCup 0 0 φ ψ = cochainCup 0 0 ψ φ := by
  have hf : frontFace 0 0 = 𝟙 ⦋0⦌ :=
    (PoolCupComparison.front_subinterval 0 0).trans (TauCeti.SimplexCategory.subinterval_zero_eq_id _)
  have hb : backFace 0 0 = 𝟙 ⦋0⦌ :=
    (PoolCupComparison.back_subinterval 0 0).trans (TauCeti.SimplexCategory.subinterval_zero_eq_id _)
  apply cochain_ext
  intro σ
  rw [cochainCup_eval, cochainCup_eval]
  unfold frontSimplex backSimplex
  rw [hf, hb]
  simp only [op_id, Functor.map_id_apply]
  exact mul_comm _ _

theorem cochain_zero_comm (P : TopPair.{0}) (φ : singularCochainGroup (ZMod 2) P.fst 0)
    (ψ : relative P 0) :
    RelativeCupCochain.cup P 0 0 φ ψ = RelativeCupOne.rightCup P 0 0 ψ φ := by
  apply toAmbient_injective P 0
  exact (toAmbient_cup P 0 0 φ ψ).trans
    ((absolute_cochain_zero_comm P.fst φ (toAmbient P 0 ψ)).trans
      (RelativeCupOne.toAmbient_rightCup P 0 0 ψ φ).symm)

private theorem cast_closed (P : TopPair.{0}) {m n : ℕ} (h : m = n) (ψ : relative P m)
    (hψ : differential P m ψ = 0) : differential P n (cast P h ψ) = 0 := by
  subst n
  exact hψ

private theorem castClass_trans (P : TopPair.{0}) {i j k : ℕ} (h : i = j) (h' : j = k)
    (a : RelativeCup.cohomology P i) :
    CupBoundary.castClass P h' (CupBoundary.castClass P h a) =
      CupBoundary.castClass P (h.trans h') a := by
  subst j
  subst k
  rfl

theorem positive_comm (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n + 1)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) (hψ : differential P q ψ = 0) :
    CupBoundary.castClass P h
        (RelativeCup.cup P p q (cocycleClass P.fst p φ hφ)
          (CochainClass.classOf (RelativeCup.cx P) q ψ hψ)) =
      CupBoundary.castClass P (by omega : q + p = n + 1)
        (CochainClass.classOf (RelativeCup.cx P) (q + p) (RelativeCupOne.rightCup P q p ψ φ)
          (RelativeCupOne.rightCup_closed P q p ψ φ hψ hφ)) := by
  let L := RelativeCupCochain.cup P p q φ ψ
  let R := RelativeCupOne.rightCup P q p ψ φ
  have hL := preserves_cocycles P p q φ ψ hφ hψ
  have hR := RelativeCupOne.rightCup_closed P q p ψ φ hψ hφ
  have hLc := cast_closed P h L hL
  have hRc := cast_closed P (by omega : q + p = n + 1) R hR
  have hc := classOf_eq_of_boundary (RelativeCup.cx P) n (n + 1)
    (RelativeCupOne.one P p q n h φ ψ) (cast P h L) (cast P (by omega) R) hLc hRc
    (RelativeCupOne.boundary_cocycles P p q n h φ ψ hφ hψ).symm
  exact (congrArg (CupBoundary.castClass P h) (RelativeCup.cup_mk P p q φ hφ ψ hψ)).trans
    ((CupBoundary.castClass_classOf P h L hL hLc).trans
      (hc.trans (CupBoundary.castClass_classOf P (by omega) R hR hRc).symm))

/-- Every degree is included; the zero-degree case is handled at actual cochain level. -/
theorem comm (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) (hψ : differential P q ψ = 0) :
    RelativeCup.cup P p q (cocycleClass P.fst p φ hφ)
        (CochainClass.classOf (RelativeCup.cx P) q ψ hψ) =
      CupBoundary.castClass P (Nat.add_comm q p)
        (CochainClass.classOf (RelativeCup.cx P) (q + p) (RelativeCupOne.rightCup P q p ψ φ)
          (RelativeCupOne.rightCup_closed P q p ψ φ hψ hφ)) := by
  by_cases hz : p + q = 0
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    have hc := cochain_zero_comm P φ ψ
    exact (RelativeCup.cup_mk P 0 0 φ hφ ψ hψ).trans
      (CochainClass.classOf_congr (RelativeCup.cx P) 0 hc _ _)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, p + q = n + 1 := ⟨p + q - 1, by omega⟩
    apply CupIteration.relativeCast_injective P hn
    rw [castClass_trans]
    exact positive_comm P p q n hn φ ψ hφ hψ


end
end Finsler.RelativeCupCommutativity
