module

public import Finsler.Topology.SupportedDoubleCap
public import Finsler.Topology.AnnularCutComparison

/-! Identify the actual existing annular tested cut with its genuine
localized double-cap output, preceded by the specified small-chain
retraction. The retraction is kept in the chain formula. -/

@[expose] public section
namespace Finsler.AnnularDoubleCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def localDomain (q : ℕ) :
    (small (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r))).X ((m + p) + q + 1) ⟶
        (chains (TopCat.of (neighborhood (m + 1) r))).X q :=
  SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
    (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + p) + q + 1) (by omega)

def localOutput (q : ℕ) :
    (small (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r))).X ((m + p) + q + 1) ⟶
        (chains (TopCat.of (SphereLoop (m + 1)))).X q :=
  localDomain m p h hr T q ≫ (push (TopCat.ofHom (retained (m + 1) hr))).f q

theorem domain_inclusion (q : ℕ) :
    localDomain m p h hr T q ≫
        (push (SupportedCap.subspaceMap (parameters (m + 1)) (neighborhood (m + 1) r))).f q =
      (inclusion (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
        (exterior (m + 1) ρ) (neighborhood (m + 1) r))).f ((m + p) + q + 1) ≫
      RelativeCapAssociativity.absoluteChain (parameters (m + 1)) (m + 1) (p + q) ((m + p) + q + 1)
        (by omega) (AnnularSelfCut.cocycle (m + 1) (by omega) h) ≫
      RelativeCapAssociativity.absoluteChain (parameters (m + 1)) p q (p + q) rfl
        (TubeCochainExtension.extend (parameters (m + 1)) (neighborhood (m + 1) r) p
          (NormalizedSelfCut.testedCocycle (m + 1) p hr T)) :=
  SupportedDoubleCap.localized_inclusion _ _ _ _ _ _ _ _ q ((m + p) + q + 1) (by omega)

theorem cut_eq_retraction
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    AnnularCutComparison.cut m p h hρr hr T hT q =
      (TauCeti.smallSingularRetraction coeff (SupportedCap.cover (parameters (m + 1))
        (exterior (m + 1) ρ) (neighborhood (m + 1) r))
        (SupportedCap.cover_open _ _ _ (exterior_open _ _) (neighborhood_open _ _))
        (SupportedCap.cover_univ _ _ _ (cover (m + 1) hρr))).f ((m + p) + q + 1) ≫
      localOutput m p h hr T q := by
  simp only [AnnularCutComparison.cut, localOutput, localDomain, SupportedDoubleCap.localized,
    SupportedCap.cut, NormalizedSelfCut.testedOperation, DegreeLoweringHomology.Map.post,
    SupportedCapHomology.absoluteOperation, Category.assoc]

theorem cut_on_small {Z : TopCat.{0}} {ι : Type*} (W : ι → Set Z) (f : Z ⟶ parameters (m + 1))
    (e : small Z W ⟶ small (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r)))
    (he : e ≫ inclusion (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r)) = inclusion Z W ≫ push f)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    (inclusion Z W).f ((m + p) + q + 1) ≫ (push f).f ((m + p) + q + 1) ≫
      AnnularCutComparison.cut m p h hρr hr T hT q =
      e.f ((m + p) + q + 1) ≫ localOutput m p h hr T q := by
  let r' := TauCeti.smallSingularRetraction coeff (SupportedCap.cover (parameters (m + 1))
    (exterior (m + 1) ρ) (neighborhood (m + 1) r))
    (SupportedCap.cover_open _ _ _ (exterior_open _ _) (neighborhood_open _ _))
    (SupportedCap.cover_univ _ _ _ (cover (m + 1) hρr))
  have hr' : inclusion (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r)) ≫ r' = 𝟙 _ :=
    TauCeti.ι_comp_smallSingularRetraction coeff _ _ _
  have hi : (inclusion Z W ≫ push f) ≫ r' = e := by
    rw [← he, Category.assoc, hr', Category.comp_id]
  rw [cut_eq_retraction]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun g => g.f ((m + p) + q + 1) ≫ localOutput m p h hr T q) hi

theorem canonical_cut_eq
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    eqToHom (congrArg (chains (parameters (m + 1))).X
      (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
        AnnularCutComparison.cut m p h hρr hr T hT q =
      SupportedDoubleCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.testedCocycle (m + 1) p hr T)
        (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        q ((m + 1) + (p + q)) rfl ≫ (push (TopCat.ofHom (retained (m + 1) hr))).f q := by
  have aux (N : ℕ) (he : N = (m + p) + q + 1) (hN : (m + 1) + (p + q) = N) :
      eqToHom (congrArg (chains (parameters (m + 1))).X he) ≫
          AnnularCutComparison.cut m p h hρr hr T hT q =
        SupportedDoubleCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
          (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
          (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
          (NormalizedSelfCut.testedCocycle (m + 1) p hr T)
          (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
          q N hN ≫ (push (TopCat.ofHom (retained (m + 1) hr))).f q := by
    subst N
    rw [eqToHom_refl, Category.id_comp]
    rfl
  exact aux _ (by omega) rfl

theorem canonical_cut_on_small {Z : TopCat.{0}} {ι : Type*} (W : ι → Set Z)
    (f : Z ⟶ parameters (m + 1))
    (e : small Z W ⟶ small (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r)))
    (he : e ≫ inclusion (parameters (m + 1)) (SupportedCap.cover (parameters (m + 1))
      (exterior (m + 1) ρ) (neighborhood (m + 1) r)) = inclusion Z W ≫ push f)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    (inclusion Z W).f ((m + 1) + (p + q)) ≫ (push f).f ((m + 1) + (p + q)) ≫
      eqToHom (congrArg (chains (parameters (m + 1))).X
        (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
        AnnularCutComparison.cut m p h hρr hr T hT q =
      e.f ((m + 1) + (p + q)) ≫
        SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
          (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
          (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
          (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl ≫
        (push (TopCat.ofHom (retained (m + 1) hr))).f q := by
  rw [canonical_cut_eq]
  have hs := SupportedDoubleCap.cut_on_small (parameters (m + 1)) (exterior (m + 1) ρ)
    (neighborhood (m + 1) r) (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
    (NormalizedSelfCut.testedCocycle (m + 1) p hr T)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) W f e he q ((m + 1) + (p + q)) rfl
  simpa only [Category.assoc] using congrArg
    (fun g => g ≫ (push (TopCat.ofHom (retained (m + 1) hr))).f q) hs

end
end Finsler.AnnularDoubleCap
