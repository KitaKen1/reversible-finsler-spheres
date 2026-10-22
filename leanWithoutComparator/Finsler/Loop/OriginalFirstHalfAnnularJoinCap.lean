module

public import Finsler.Loop.OriginalFirstHalfAnnularJoinCover
public import Finsler.Loop.NormalizedCapTimePrism

/-! Actual annular-cylinder join localization and strict cap/prism
identity in the genuine near-pair cylinder, before any gamma retraction. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfAnnularJoinCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.OriginalFirstHalfCupOneCochains
open Finsler.OriginalFirstHalfAnnularJoinCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem cap_cast (X : TopCat.{0}) (a q N : ℕ) (h : a + q = N)
    (φ : singularCochainGroup (ZMod 2) X a) :
    eqToHom (congrArg (chains X).X h.symm) ≫ absoluteChain X a q (a + q) rfl φ =
      absoluteChain X a q N h φ := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ)
  {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

include hκR in
theorem parent_near (q : ℕ)
    (τ : ((ambient α β).smallSingularSubcomplex (cover α β κ) : SSet) _⦋(m + 1) + q⦌)
    (hτ : (TopCat.toSSet.obj (ambient α β)).ιChainComplex τ.val ≫
      absoluteChain (ambient α β) (m + 1) q ((m + 1) + q) rfl (join α β hκ) ≠ 0) :
    Set.range ((ambient α β).toSSetObjEquiv _ τ.val) ⊆ OriginalFirstHalfJoinTimeCover.pairDomain α β R := by
  obtain ⟨⟨x, y⟩, hs⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β)
    (cover α β κ) τ.val).mp τ.property
  rcases PairDistanceCover.near_far_rectangle (fun x => basepoint (α x))
    (fun y => basepoint (β y)) κ x y with hfar | hnear
  · have hf : Set.range ((ambient α β).toSSetObjEquiv _ τ.val) ⊆ joinFar α β κ := by
      intro z hz
      exact hfar z.2.1 (hs hz).1 z.2.2 (hs hz).2
    exact (hτ (SupportedCap.cap_zero_on_simplex _ _ (m + 1) q ((m + 1) + q) rfl
      (join α β hκ) (join_far_zero α β hκ) τ.val hf)).elim
  · intro z hz
    exact (hnear z.2.1 (hs hz).1 z.2.2 (hs hz).2).le.trans hκR

def localized : DegreeLoweringHomology.Map (small (ambient α β) (cover α β κ))
    (chains (TopCat.of (OriginalFirstHalfJoinTimeCover.pairDomain α β R))) (m + 1) :=
  CapOutputSupport.operation (X := ambient α β) (Y := ambient α β) (cover α β κ) (𝟙 _)
    (OriginalFirstHalfJoinTimeCover.pairDomain α β R) (m + 1) (join α β hκ)
    (fun q τ hτ z hz => parent_near α β R hκ hκR q τ hτ hz) (join_closed α β hκ)

def native : DegreeLoweringHomology.Map (small (ambient α β) (cover α β κ))
    (chains (OriginalFirstHalfZeroCover.space α β R)) (m + 1) :=
  (localized α β R hκ hκR).post (push (OriginalFirstHalfJoinTimeCover.pairIso α β R).inv)

theorem source (q : ℕ) : (native α β R hκ hκR).component q ≫ (push (nearSource α β R)).f q =
    (inclusion (ambient α β) (cover α β κ)).f ((m + 1) + q) ≫
      absoluteChain (ambient α β) (m + 1) q ((m + 1) + q) rfl (join α β hκ) := by
  have hm : (OriginalFirstHalfJoinTimeCover.pairIso α β R).inv ≫ nearSource α β R =
      SupportedCap.subspaceMap (ambient α β) (OriginalFirstHalfJoinTimeCover.pairDomain α β R) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have hi := CapOutputSupport.component_inclusion (X := ambient α β) (Y := ambient α β)
    (cover α β κ) (𝟙 _) (OriginalFirstHalfJoinTimeCover.pairDomain α β R) (m + 1) (join α β hκ)
    (fun q τ hτ z hz => parent_near α β R hκ hκR q τ hτ hz) q
  have hid : push (𝟙 (ambient α β)) = 𝟙 (chains (ambient α β)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (ambient α β))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [hid, HomologicalComplex.id_f, Category.comp_id] at hi
  dsimp only [native, DegreeLoweringHomology.Map.post]
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← push_comp, hm]
  exact hi

theorem source_succ (q : ℕ) :
    eqToHom (congrArg (small (ambient α β) (cover α β κ)).X
      (show (m + 1) + q + 1 = (m + 1) + (q + 1) by omega)) ≫
      (native α β R hκ hκR).component (q + 1) ≫ (push (nearSource α β R)).f (q + 1) =
    (inclusion (ambient α β) (cover α β κ)).f ((m + 1) + q + 1) ≫
      absoluteChain (ambient α β) (m + 1) (q + 1) ((m + 1) + q + 1) (by omega) (join α β hκ) := by
  rw [source, ← Category.assoc,
    transport_f (inclusion (ambient α β) (cover α β κ)) ((m + 1) + q + 1) ((m + 1) + (q + 1)) (by omega),
    Category.assoc, cap_cast (ambient α β) (m + 1) (q + 1) ((m + 1) + q + 1) (by omega)]

theorem prism_cap (q : ℕ) :
    prism α β κ ((m + 1) + q) ≫
      eqToHom (congrArg (small (ambient α β) (cover α β κ)).X
        (show (m + 1) + q + 1 = (m + 1) + (q + 1) by omega)) ≫
          (native α β R hκ hκR).component (q + 1) =
    (CompactJoinCapLocalization.localized α β (by omega) hκ hκR).component q ≫
      AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) q := by
  haveI := nearSource_mono α β R (q + 1)
  apply (cancel_mono ((push (nearSource α β R)).f (q + 1))).mp
  calc
    _ = prism α β κ ((m + 1) + q) ≫
        (inclusion (ambient α β) (cover α β κ)).f ((m + 1) + q + 1) ≫
          absoluteChain (ambient α β) (m + 1) (q + 1) ((m + 1) + q + 1) (by omega) (join α β hκ) := by
      simp only [Category.assoc]
      rw [source_succ]
    _ = (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f ((m + 1) + q) ≫
        absoluteChain (TopCat.of (P × Q)) (m + 1) q ((m + 1) + q) rfl
          (CompactJoinCocycle.cocycle α β (by omega) hκ) ≫ AnnularTimeTrim.prism (TopCat.of (P × Q)) q := by
      rw [← Category.assoc, ← prism_inclusion, Category.assoc]
      exact congrArg (fun k => (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f
        ((m + 1) + q) ≫ k) (NormalizedCapTimePrism.annular_cap (TopCat.of (P × Q)) (m + 1) q
          (CompactJoinCocycle.cocycle α β (by omega) hκ) (CompactJoinCocycle.cocycle_normalized α β (by omega) hκ))
    _ = ((CompactJoinCapLocalization.localized α β (by omega) hκ hκR).component q ≫
        (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f q) ≫
          AnnularTimeTrim.prism (TopCat.of (P × Q)) q := by
      rw [CompactJoinCapLocalization.source]
      simp only [Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using (congrArg
        (fun k => (CompactJoinCapLocalization.localized α β (by omega) hκ hκR).component q ≫ k)
        (near_prism_source α β R q)).symm

end
end Finsler.OriginalFirstHalfAnnularJoinCap
