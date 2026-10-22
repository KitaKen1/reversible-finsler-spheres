module

public import Finsler.Topology.RelativeCapAssociativity
public import Finsler.Topology.DualConnecting

@[expose] public section

namespace Finsler.RelativeCapBoundary

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SphereOddDegree Finsler.CochainComparison Finsler.RelativeCap
open Finsler.RelativeCapAssociativity

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

theorem absolute_chain_boundary (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    absoluteChain X p (q + 1) (n + 1) (by omega) φ ≫ (absolute X).d (q + 1) q =
      (absolute X).d (n + 1) n ≫ absoluteChain X p q n h φ := by
  have hz : ((TopCat.toSSet.obj X).chainComplex (𝟙_ (ModuleCat (ZMod 2)))).d
      (p + 1) p ≫ φ = 0 := hφ
  have hd := TauCeti.ChainComplex.capChain_comp_d (k := ZMod 2) (diagonal X)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
    p q n h φ
  rw [hz, map_zero, sub_zero] at hd
  exact hd.trans (sign_smul p _)

theorem relative_chain_boundary (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) P.fst p)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    chain P p (q + 1) (n + 1) (by omega) φ ≫ (relative P).d (q + 1) q =
      (relative P).d (n + 1) n ≫ chain P p q n h φ := by
  have hz : (absolute P.fst).d (p + 1) p ≫ φ = 0 := hφ
  have hd := TauCeti.ChainComplex.capChain_comp_d (k := ZMod 2)
    (relativeDiagonal P) (unitAction P) p q n h φ
  rw [hz, map_zero, sub_zero] at hd
  exact hd.trans (sign_smul p _)

theorem absolute_chain_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
    (p q n : ℕ) (h : p + q = n) (φ : singularCochainGroup (ZMod 2) Y p) :
    absoluteChain X p q n h (cochainPullback f p φ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) coeff).f q =
      (SSet.chainComplexMap (TopCat.toSSet.map f) coeff).f n ≫
        absoluteChain Y p q n h φ := by
  exact TauCeti.ChainComplex.capChain_naturality (k := ZMod 2)
    (diagonal Y) ((TopCat.toSSet.obj Y).chainComplexPairing
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
    (diagonal X) ((TopCat.toSSet.obj X).chainComplexPairing
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
    (SSet.chainComplexMap (TopCat.toSSet.map f) coeff)
    (SSet.chainComplexMap (TopCat.toSSet.map f) coeff)
    (SSet.chainComplexMap (TopCat.toSSet.map f) coeff)
    (SSet.chainComplexMap (TopCat.toSSet.map f) coeff)
    (TopCat.alexanderWhitneyDiagonal_naturality f (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv)
    (SSet.chainComplexPairing_naturality (TopCat.toSSet.map f)
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom).symm p q n h φ

abbrev absoluteCycleOf (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :=
  TauCeti.ChainComplex.capCycles (ZMod 2) (diagonal X)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
    p q n h ((native X).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)

theorem absolute_cycle_i (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    absoluteCycleOf X p q n h φ hφ ≫ (absolute X).iCycles q =
      (absolute X).iCycles n ≫ absoluteChain X p q n h φ := by
  refine (TauCeti.ChainComplex.capCycles_i (diagonal X)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
    p q n h ((native X).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)).trans ?_
  exact congrArg (fun z => (absolute X).iCycles n ≫ absoluteChain X p q n h z)
    ((native X).i_cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)

theorem absolute_cap_class (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (absolute X).homologyπ n ≫ ModuleCat.ofHom (PoolCap.cap X p q n h (cocycleClass X p φ hφ)) =
      absoluteCycleOf X p q n h φ hφ ≫ (absolute X).homologyπ q := by
  change (absolute X).homologyπ n ≫
    X.singularCap (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q n h
      (cohomologyEquiv X p (cocycleClass X p φ hφ)) = _
  rw [PoolCupComparison.cohomology_cocycle]
  exact TopCat.singularCap_homologyπ X (ZMod 2) (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
    (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom p q n h
    ((native X).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)

private theorem relative_cycle_i (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) P.fst p)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    cycleOf P p q n h φ hφ ≫ (relative P).iCycles q =
      (relative P).iCycles n ≫ chain P p q n h φ := by
  refine (TauCeti.ChainComplex.capCycles_i (relativeDiagonal P) (unitAction P)
    p q n h ((native P.fst).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)).trans ?_
  exact congrArg (fun z => (relative P).iCycles n ≫ chain P p q n h z)
    ((native P.fst).i_cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)

/-- Cap with an ambient class commutes with the actual homological boundary over F₂. -/
theorem boundary_cap (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 P.fst p)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff (n + 1)) :
    (P.singularHomologyδ coeff (q + 1) q rfl).hom
        (RelativeCap.cap P p (q + 1) (n + 1) (by omega) a x) =
      PoolCap.cap P.snd p q n h ((cohPullback P.map p).hom a)
        ((P.singularHomologyδ coeff (n + 1) n rfl).hom x) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective P.fst p a
  obtain ⟨c, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective (relative P) (n + 1) x
  let S := P.singularChainComplexShortComplex coeff
  have hS := P.shortExact_singularChainComplexShortComplex coeff
  have hc : (S.X₃.d (n + 1) n).hom ((S.X₃.iCycles (n + 1)).hom c) = 0 :=
    ConcreteCategory.congr_hom (S.X₃.iCycles_d (n + 1) n) c
  obtain ⟨z₂, hz₂⟩ := DualConnecting.surj_g hS (n + 1) ((S.X₃.iCycles (n + 1)).hom c)
  have hgz : (S.g.f n).hom ((S.X₂.d (n + 1) n).hom z₂) = 0 := by
    have hm := ConcreteCategory.congr_hom (S.g.comm (n + 1) n) z₂
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hm
    rw [← hm, hz₂]
    exact hc
  obtain ⟨z₁, hz₁⟩ := DualConnecting.exact_at hS n _ hgz
  have hd := hS.δ_apply (n + 1) n rfl ((S.X₃.iCycles (n + 1)).hom c)
    hc z₂ hz₂ z₁ hz₁ ((ComplexShape.down ℕ).next n) rfl
  rw [DualConnecting.cyclesMk_iCycles] at hd
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : S.X₁.cycles n,
      (hS.δ (n + 1) n rfl).hom ((S.X₃.homologyπ (n + 1)).hom c) =
        (S.X₁.homologyπ n).hom w ∧ (S.X₁.iCycles n).hom w = z₁ :=
    ⟨_, hd, HomologicalComplex.i_cyclesMk S.X₁ z₁ _ _ _⟩
  let ψ := cochainPullback P.map p φ
  have hψ := cochainPullback_cocycle P.map p φ hφ
  let c' := (cycleOf P p (q + 1) (n + 1) (by omega) φ hφ).hom c
  let z₂' := (absoluteChain P.fst p (q + 1) (n + 1) (by omega) φ).hom z₂
  let z₁' := (absoluteChain P.snd p q n h ψ).hom z₁
  have hc' : (S.X₃.d (q + 1) q).hom ((S.X₃.iCycles (q + 1)).hom c') = 0 :=
    ConcreteCategory.congr_hom (S.X₃.iCycles_d (q + 1) q) c'
  have hz₂' : (S.g.f (q + 1)).hom z₂' = (S.X₃.iCycles (q + 1)).hom c' := by
    have hq := ConcreteCategory.congr_hom
      (RelativeCapAbsolute.quotient_capChain P p (q + 1) (n + 1) (by omega) φ) z₂
    have hi := ConcreteCategory.congr_hom
      (relative_cycle_i P p (q + 1) (n + 1) (by omega) φ hφ) c
    change (S.g.f (q + 1)).hom z₂' =
      (chain P p (q + 1) (n + 1) (by omega) φ).hom ((S.g.f (n + 1)).hom z₂) at hq
    rw [hz₂] at hq
    exact hq.trans hi.symm
  have hz₁' : (S.f.f q).hom z₁' = (S.X₂.d (q + 1) q).hom z₂' := by
    have hn := ConcreteCategory.congr_hom (absolute_chain_natural P.map p q n h φ) z₁
    have hb := ConcreteCategory.congr_hom (absolute_chain_boundary P.fst p q n h φ hφ) z₂
    change (S.f.f q).hom z₁' = (absoluteChain P.fst p q n h φ).hom ((S.f.f n).hom z₁) at hn
    rw [hz₁] at hn
    exact hn.trans hb.symm
  have hd' := hS.δ_apply (q + 1) q rfl ((S.X₃.iCycles (q + 1)).hom c')
    hc' z₂' hz₂' z₁' hz₁' ((ComplexShape.down ℕ).next q) rfl
  rw [DualConnecting.cyclesMk_iCycles] at hd'
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v : S.X₁.cycles q,
      (hS.δ (q + 1) q rfl).hom ((S.X₃.homologyπ (q + 1)).hom c') =
        (S.X₁.homologyπ q).hom v ∧ (S.X₁.iCycles q).hom v = z₁' :=
    ⟨_, hd', HomologicalComplex.i_cyclesMk S.X₁ z₁' _ _ _⟩
  have hv : v = (absoluteCycleOf P.snd p q n h ψ hψ).hom w := by
    apply (ModuleCat.mono_iff_injective (S.X₁.iCycles q)).mp inferInstance
    have hi := ConcreteCategory.congr_hom (absolute_cycle_i P.snd p q n h ψ hψ) w
    change (S.X₁.iCycles q).hom ((absoluteCycleOf P.snd p q n h ψ hψ).hom w) =
      (absoluteChain P.snd p q n h ψ).hom ((S.X₁.iCycles n).hom w) at hi
    rw [hw₂] at hi
    exact hv₂.trans hi.symm
  have hin := ConcreteCategory.congr_hom
    (RelativeCap.cap_class P p (q + 1) (n + 1) (by omega) φ hφ) c
  have hout := ConcreteCategory.congr_hom (absolute_cap_class P.snd p q n h ψ hψ) w
  change RelativeCap.cap P p (q + 1) (n + 1) (by omega) (cocycleClass P.fst p φ hφ)
      ((S.X₃.homologyπ (n + 1)).hom c) = (S.X₃.homologyπ (q + 1)).hom c' at hin
  change PoolCap.cap P.snd p q n h (cocycleClass P.snd p ψ hψ)
      ((S.X₁.homologyπ n).hom w) =
    (S.X₁.homologyπ q).hom ((absoluteCycleOf P.snd p q n h ψ hψ).hom w) at hout
  rw [cohPullback_cocycleClass]
  change (hS.δ (q + 1) q rfl).hom
      (RelativeCap.cap P p (q + 1) (n + 1) (by omega) (cocycleClass P.fst p φ hφ)
        ((S.X₃.homologyπ (n + 1)).hom c)) =
    PoolCap.cap P.snd p q n h (cocycleClass P.snd p ψ hψ)
      ((hS.δ (n + 1) n rfl).hom ((S.X₃.homologyπ (n + 1)).hom c))
  exact (congrArg (hS.δ (q + 1) q rfl).hom hin).trans
    (hv₁.trans ((congrArg (S.X₁.homologyπ q).hom hv).trans
      (hout.symm.trans (congrArg (PoolCap.cap P.snd p q n h (cocycleClass P.snd p ψ hψ))
        hw₁.symm))))


end
end Finsler.RelativeCapBoundary
