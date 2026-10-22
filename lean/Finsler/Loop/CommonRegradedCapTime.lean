module

public import Finsler.Loop.RegradedSingleCapTime
public import Finsler.Loop.RegradedTimeCoverComparison
public import Finsler.Topology.PullbackPairCover

/-! Actual common-input comparison for two independent real covers of
one closed cap time model. The cap need only be closed after localization;
its identical source diagram and genuine target chain monicity identify
both common lifts. No subdivision naturality or choice of minima is assumed. -/

@[expose] public section
namespace Finsler.CommonRegradedCapTime

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable (X : TopCat.{0}) {ι κ : Type*}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set (ClosedInterval × X))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)

def common := PullbackPairCover.cover U V (𝟙 (TopCat.of (ClosedInterval × X))) (𝟙 (TopCat.of (ClosedInterval × X)))

def leftMap := SmallRefinementComparison.refinement (common X U V) U Prod.fst (fun _ _ hz => hz.1)
def rightMap := SmallRefinementComparison.refinement (common X U V) V Prod.snd (fun _ _ hz => hz.2)

include hU hV in
theorem common_open (i : ι × κ) : IsOpen (common X U V i) :=
  PullbackPairCover.isOpen (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (ClosedInterval × X))
    (Z := TopCat.of (ClosedInterval × X)) U V (𝟙 _) (𝟙 _) hU hV i

include hcU hcV in
theorem common_univ : ⋃ i, common X U V i = Set.univ :=
  PullbackPairCover.covers (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (ClosedInterval × X))
    (Z := TopCat.of (ClosedInterval × X)) U V (𝟙 _) (𝟙 _) hcU hcV

variable (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d N : ℕ) (hN : d + 1 = N)
  (cU : DegreeLoweringHomology.Map (small (TopCat.of (ClosedInterval × X)) U) E N)
  (cV : DegreeLoweringHomology.Map (small (TopCat.of (ClosedInterval × X)) V) E N)
  (C : Set (ClosedInterval × X))
  (φ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) N)
  (hφ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) C) N φ = 0)
  (j : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hj : ∀ q, Mono (j.f q))
  (hsU : ∀ q, cU.component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) U).f (N + q) ≫
      RelativeCapAssociativity.absoluteChain (TopCat.of (ClosedInterval × X)) N q (N + q) rfl φ)
  (hsV : ∀ q, cV.component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) V).f (N + q) ≫
      RelativeCapAssociativity.absoluteChain (TopCat.of (ClosedInterval × X)) N q (N + q) rfl φ)

def commonCap := cU.pre (leftMap X U V)

include hsU in
theorem common_source (q : ℕ) : (commonCap X U V E N cU).component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) (common X U V)).f (N + q) ≫
      RelativeCapAssociativity.absoluteChain (TopCat.of (ClosedInterval × X)) N q (N + q) rfl φ := by
  dsimp only [commonCap, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, hsU q, ← Category.assoc, ← HomologicalComplex.comp_f,
    leftMap, SmallRefinementComparison.refinement_inclusion]

include hj hsU hsV in
theorem right_component (q : ℕ) :
    (rightMap X U V).f (N + q) ≫ cV.component q = (commonCap X U V E N cU).component q := by
  have : Mono (j.f q) := hj q
  apply (cancel_mono (j.f q)).mp
  rw [Category.assoc, hsV q, common_source X U V E N cU φ j hsU q,
    ← Category.assoc, ← HomologicalComplex.comp_f, rightMap, SmallRefinementComparison.refinement_inclusion]

variable (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ C) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ C)

include hj hsU hsV in
theorem homology_eq (q : ℕ) :
    (RegradedSingleCapTime.operation X U hU hcU E d N hN cU C φ hφ j hj hsU h₀ h₁).homology q =
    (RegradedSingleCapTime.operation X V hV hcV E d N hN cV C φ hφ j hj hsV h₀ h₁).homology q := by
  let c := commonCap X U V E N cU
  let hs := common_source X U V E N cU φ j hsU
  let w := RegradedSingleCapTime.operation X (common X U V) (common_open X U V hU hV)
    (common_univ X U V hcU hcV) E d N hN c C φ hφ j hj hs h₀ h₁
  have hleft : (RegradedSingleCapTime.operation X U hU hcU E d N hN cU C φ hφ j hj hsU h₀ h₁).homology q = w.homology q := by
    apply RegradedTimeCoverComparison.homology_eq (common X U V) U Prod.fst (fun _ _ hz => hz.1)
      (common_open X U V hU hV) (common_univ X U V hcU hcV) hU hcU X
      (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
      ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) E d N hN cU
    · intro k
      rfl
    · intro k
      simp only [w, c, commonCap, RegradedSingleCapTime.component_normal,
        DegreeLoweringHomology.Map.pre, HomologicalComplex.comp_f, leftMap, Category.assoc]
      rfl
  have hright : (RegradedSingleCapTime.operation X V hV hcV E d N hN cV C φ hφ j hj hsV h₀ h₁).homology q = w.homology q := by
    apply RegradedTimeCoverComparison.homology_eq (common X U V) V Prod.snd (fun _ _ hz => hz.2)
      (common_open X U V hU hV) (common_univ X U V hcU hcV) hV hcV X
      (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
      ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) E d N hN cV
    · intro k
      rfl
    · intro k
      change w.component k = _
      rw [show w.component k = ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).hom (d + k) (d + k + 1) ≫
        eqToHom (congrArg (chains (TopCat.of (ClosedInterval × X))).X (show d + k + 1 = N + k by omega)) ≫
        (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff (common X U V)
          (common_open X U V hU hV) (common_univ X U V hcU hcV)).f (N + k) ≫
        (commonCap X U V E N cU).component k from rfl]
      rw [← right_component X U V E N cU cV φ j hj hsU hsV k]
      simp only [HomologicalComplex.comp_f, rightMap, Category.assoc]
  exact hleft.trans hright.symm

end
end Finsler.CommonRegradedCapTime
