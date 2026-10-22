module

public import Finsler.Analysis.H1NearJoin
public import Finsler.Topology.SmallChainCarrier
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! The actual controlled near-join on the project's F₂ singular chains.
Boundary and support use the genuine functor; the correction prism lives in
the original q+ε cut. The diagonal Thom cut and interchange are still separate. -/

@[expose] public section

namespace Finsler.NearJoinChains

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.H1NearJoin

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def push {X Y : TopCat.{0}} (f : X ⟶ Y) : chains X ⟶ chains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) coeff

/-- Actual chains supported in V are sent to chains supported in the image family. -/
theorem image_supported {X Y : TopCat.{0}} (f : X ⟶ Y) {ι : Type*}
    (V : ι → Set X) {n : ℕ} {c : coeff ⟶ (chains X).X n}
    (hc : c ∈ supported X V n) :
    c ≫ (push f).f n ∈ supported Y (fun i => f '' V i) n := by
  let W : ι → Set Y := fun i => f '' V i
  have hm : ∀ i, Set.MapsTo f (V i) (W i) := fun i x hx => ⟨x, hx, rfl⟩
  let m := SSet.chainComplexMap (X.smallSingularSubcomplexMap V W f id hm) coeff
  have he : m ≫ Finsler.SmallChainCarrier.inclusion Y W = Finsler.SmallChainCarrier.inclusion X V ≫ push f := by
    simpa only [m, Finsler.SmallChainCarrier.inclusion, push, Functor.map_comp] using
      congrArg (fun g => SSet.chainComplexMap g coeff)
        (TopCat.smallSingularSubcomplexMap_ι V W f id hm)
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hc
  refine (TauCeti.mem_smallSingularChains_iff _).mpr ⟨g ≫ m.f n, ?_⟩
  rw [Category.assoc, ← HomologicalComplex.comp_f, he,
    HomologicalComplex.comp_f, ← Category.assoc]

def nearJoinMorphism {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    TopCat.of (tube F p hq hε) ⟶ TopCat.of (lev F (p + (q + ε))) :=
  TopCat.ofHom (nearJoin F hp hq hε)

def joinChainMap {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :=
  push (nearJoinMorphism F hp hq hε)

theorem join_boundary {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (i j : ℕ) :
    (joinChainMap F hp hq hε).f i ≫ (chains (TopCat.of (lev F (p + (q + ε))))).d i j =
      (chains (TopCat.of (tube F p hq hε))).d i j ≫ (joinChainMap F hp hq hε).f j :=
  (joinChainMap F hp hq hε).comm i j

theorem join_supported {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) {ι : Type*}
    (V : ι → Set (tube F p hq hε)) {k : ℕ}
    {c : coeff ⟶ (chains (TopCat.of (tube F p hq hε))).X k}
    (hc : c ∈ supported (TopCat.of (tube F p hq hε)) V k) :
    c ≫ (joinChainMap F hp hq hε).f k ∈
      supported (TopCat.of (lev F (p + (q + ε))))
        (fun i => nearJoinMorphism F hp hq hε '' V i) k :=
  image_supported (nearJoinMorphism F hp hq hε) V hc

def correctionChainHomotopy {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    _root_.Homotopy (push (TopCat.ofHom (originalSecond F p hq hε)))
      (push (TopCat.ofHom (correctedSecond F p hq hε))) := by
  let H : TopCat.Homotopy (TopCat.ofHom (originalSecond F p hq hε))
      (TopCat.ofHom (correctedSecond F p hq hε)) := correctionHomotopy F p hq hε
  exact H.toSSet.chainComplexMap coeff

theorem correction_homology_eq {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    HomologicalComplex.homologyMap (push (TopCat.ofHom (originalSecond F p hq hε))) k =
      HomologicalComplex.homologyMap (push (TopCat.ofHom (correctedSecond F p hq hε))) k :=
  (correctionChainHomotopy F p hq hε).homologyMap_eq k


end
end Finsler.NearJoinChains
