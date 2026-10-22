module

public import Finsler.Topology.NormalizedDiagonalCocycle
public import Finsler.Topology.SupportedSelfCut

/-! The normalized actual self-cut Thom stage, its literal time-end cochain
vanishing, and the actual T-cap followed by C2. The genuine time-interval
cross and its endpoint cancellation on small chains remain separate. -/

@[expose] public section
namespace Finsler.NormalizedSelfCut

open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle
open Finsler.SupportedSelfCut
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def cocycle (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (parameters n) n :=
  cochainPullback (selfEvaluation n) n (NormalizedDiagonalCocycle.ambient n hn hρ)

theorem cocycle_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (parameters n) n (cocycle n hn hρ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (selfEvaluation n).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)

theorem cocycle_normalized (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (parameters n))
      (cocycle n hn hρ) := by
  have he : cocycle n hn hρ = SingularNormalization.normalize (parameters n) n
      (SelfCutThomCocycle.cocycle n hn hρ) :=
    SingularNormalization.normalize_natural (selfEvaluation n) n _
  rw [he]
  exact SingularNormalization.normalize_degeneracies _ n _

theorem time_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (atTime n 0) n (cocycle n hn hρ) = 0 := by
  change cochainPullback (atTime n 0) n (cochainPullback (selfEvaluation n) n _) = 0
  rw [← SupportedCapNaturality.pullback_comp, time_factor]
  exact NormalizedDiagonalCocycle.pullback_zero_of_diagonal hn hρ (timeEvaluation n 0)
    (fun _ => rfl)

theorem time_one (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (atTime n 1) n (cocycle n hn hρ) = 0 := by
  change cochainPullback (atTime n 1) n (cochainPullback (selfEvaluation n) n _) = 0
  rw [← SupportedCapNaturality.pullback_comp, time_factor]
  exact NormalizedDiagonalCocycle.pullback_zero_of_diagonal hn hρ (timeEvaluation n 1)
    (fun u => (sphereRepresentative_endpoints u).symm)

theorem cocycle_supported (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) n
      (cocycle n hn hρ) = 0 := by
  rw [cocycle, ← SupportedCapNaturality.pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_far hn hρ
  intro z
  exact z.property.le

def operation (n : ℕ) (hn : 1 ≤ n) {ρ r : ℝ} (hρ : 0 < ρ) (hr : ρ < r) :=
  SupportedCapHomology.operation (parameters n) (exterior n ρ) (neighborhood n r)
    (exterior_open n ρ) (neighborhood_open n r) (cover n hr) n
    (cocycle n hn hρ) (cocycle_supported n hn hρ) (cocycle_closed n hn hρ)

def testedCocycle (n p : ℕ) {r : ℝ} (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (TopCat.of (neighborhood n r)) p :=
  cochainPullback (TopCat.ofHom (tested n hr)) p T

theorem testedCocycle_closed (n p : ℕ) {r : ℝ} (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (neighborhood n r)) p (testedCocycle n p hr T) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (TopCat.of (SphereLoop n)))
    (singularCochainComplexZMod2.map (TopCat.ofHom (tested n hr)).op) p T hT

def testedOperation (n p : ℕ) {r : ℝ} (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :=
  (SupportedCapHomology.absoluteOperation (TopCat.of (neighborhood n r)) p
    (testedCocycle n p hr T) (testedCocycle_closed n p hr T hT)).post
      (SupportedCapNaturality.push (TopCat.ofHom (retained n hr)))

def chainCut (n p : ℕ) (hn : 1 ≤ n) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    (chains (parameters n)).X (n + (p + q)) ⟶ (chains (TopCat.of (SphereLoop n))).X q :=
  (operation n hn hρ hρr).component (p + q) ≫ (testedOperation n p hr T hT).component q

theorem chainCut_boundary (n p : ℕ) (hn : 1 ≤ n) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    chainCut n p hn hρ hρr hr T hT (q + 1) ≫
        (chains (TopCat.of (SphereLoop n))).d (q + 1) q =
      (chains (parameters n)).d (n + (p + (q + 1))) (n + (p + q)) ≫
        chainCut n p hn hρ hρr hr T hT q := by
  have hu : (operation n hn hρ hρr).component (p + (q + 1)) ≫
      (chains (TopCat.of (neighborhood n r))).d (p + (q + 1)) (p + q) =
    (chains (parameters n)).d (n + (p + (q + 1))) (n + (p + q)) ≫
      (operation n hn hρ hρr).component (p + q) :=
    (operation n hn hρ hρr).comm (p + q)
  unfold chainCut
  rw [Category.assoc, (testedOperation n p hr T hT).comm,
    ← Category.assoc, hu, Category.assoc]

end
end Finsler.NormalizedSelfCut
