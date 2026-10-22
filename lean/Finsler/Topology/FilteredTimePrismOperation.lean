module

public import Finsler.Topology.RefinedAnnularCollar
public import Finsler.Topology.AnnularTimeTrim
public import Finsler.Topology.TimePrismDescent

/-! A genuine closed filtered cut along an actual cylinder defines a
degree-lowering filtered time operation when its original endpoint
images lie in the annular collar. Source approximation preserves those
images, so no additional endpoint-smallness hypothesis is required. -/

@[expose] public section
namespace Finsler.FilteredTimePrismOperation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

def along (X Z : TopCat.{0}) (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (v : ∀ q, (chains Z).X (d + q + 1) ⟶ E.X q)
    (f : TopCat.of (ClosedInterval × X) ⟶ Z) (q : ℕ) :
    (chains (TopCat.of (ClosedInterval × X))).X (d + q + 1) ⟶ E.X q :=
  (push f).f (d + q + 1) ≫ v q

theorem along_comm (X Z : TopCat.{0}) (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (v : ∀ q, (chains Z).X (d + q + 1) ⟶ E.X q)
    (f : TopCat.of (ClosedInterval × X) ⟶ Z)
    (hv : ∀ q, v (q + 1) ≫ E.d (q + 1) q =
      (chains Z).d (d + q + 2) (d + q + 1) ≫ v q) (q : ℕ) :
    along X Z E d v f (q + 1) ≫ E.d (q + 1) q =
      (chains (TopCat.of (ClosedInterval × X))).d (d + q + 2) (d + q + 1) ≫ along X Z E d v f q := by
  dsimp [along]
  rw [Category.assoc, hv q]
  simpa only [Nat.add_succ, Nat.add_zero, Category.assoc] using
    congrArg (fun k => k ≫ v q) ((push f).comm (d + q + 2) (d + q + 1))

variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (X Z : TopCat.{0}) {ι : Type*} (U : ι → Set Z) (g : Z ⟶ parameters (m + 1))
  (B : Set (SphereLoop (m + 1)))
  (v : ∀ q, (chains Z).X ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q)
  (hv : ∀ q, v q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
    (TauCeti.singularSmallApprox (X := Z) coeff U).f ((m + p) + q + 1) ≫
      (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)
  (f : TopCat.of (ClosedInterval × X) ⟶ Z)

include hv

theorem along_endpoint (t : ClosedInterval)
    (ht : ∀ x, distance (m + 1) (g (f (t, x))) ≤ δ) (q : ℕ) :
    (push (AnnularTimeTrim.slice X t)).f ((m + p) + q + 1) ≫
      along X Z (chains (TopCat.of B)) (m + p) v f q = 0 := by
  have hh := RefinedAnnularCollar.filtered_map_zero m p h hρr hr T hT
    (Y := X) (Z := Z) U g B v hv (AnnularTimeTrim.slice X t ≫ f) ht q
  simpa only [along, push_comp, HomologicalComplex.comp_f, Category.assoc] using hh

def operation
    (hcomm : ∀ q, v (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (chains Z).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ v q)
    (h₀ : ∀ x, distance (m + 1) (g (f (0, x))) ≤ δ)
    (h₁ : ∀ x, distance (m + 1) (g (f (1, x))) ≤ δ) :
    DegreeLoweringHomology.Map (chains X) (chains (TopCat.of B)) (m + p) :=
  TimePrismDescent.operation ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff)
    (m + p) (along X Z (chains (TopCat.of B)) (m + p) v f)
    (along_comm X Z (chains (TopCat.of B)) (m + p) v f hcomm)
    (along_endpoint m p h hρr hr T hT X Z U g B v hv f 0 h₀)
    (along_endpoint m p h hρr hr T hT X Z U g B v hv f 1 h₁)

end
end Finsler.FilteredTimePrismOperation
