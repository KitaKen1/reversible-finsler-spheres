module

public import Finsler.Topology.AnnularTrimHomology

/-! Actual interior-time trimming for an arbitrary genuine self-cut
cylinder, so the two joined-half cylinders may use one common collar. -/

@[expose] public section
namespace Finsler.CylinderTimeTrim

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X : Type} [TopologicalSpace X] {n : ℕ}

def trimmedMap (f : TopCat.of (ClosedInterval × X) ⟶ parameters n)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    TopCat.of (ClosedInterval × X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => f (InteriorTimeSlide.trimTime a ha ha1 z.1, z.2),
    f.hom.continuous.comp (((InteriorTimeSlide.trimTime a ha ha1).continuous.comp
      continuous_fst).prodMk continuous_snd)⟩

def homotopy (f : TopCat.of (ClosedInterval × X) ⟶ parameters n)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) : TopCat.Homotopy f (trimmedMap f a ha ha1) where
  toFun z := f (InteriorTimeSlide.slide a ha ha1 (z.1, z.2.1), z.2.2)
  continuous_toFun := f.hom.continuous.comp (((InteriorTimeSlide.slide a ha ha1).continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd))
  map_zero_left z := by
    change f (InteriorTimeSlide.slide a ha ha1 (0, z.1), z.2) = f z
    rw [InteriorTimeSlide.slide_zero]
  map_one_left z := by
    change f (InteriorTimeSlide.slide a ha ha1 (1, z.1), z.2) =
      f (InteriorTimeSlide.trimTime a ha ha1 z.1, z.2)
    rw [InteriorTimeSlide.slide_one]

section
variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (f : TopCat.of (ClosedInterval × X) ⟶ parameters (m + 1))
  (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)

def comparison (q : ℕ) : (chains (TopCat.of X)).X ((m + p) + q) ⟶
    (chains (TopCat.of (SphereLoop (m + 1)))).X (q + 1) :=
  AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
    ((homotopy f a ha ha1).toSSet.chainComplexMap coeff).hom
      ((m + p) + q + 1) ((m + p) + q + 2) ≫
        AnnularCutComparison.cut m p h hρr hr T hT (q + 1)

theorem side_zero (t : ClosedInterval)
    (ht : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (homotopy f a ha ha1 (s, (t, x))) ≤ δ) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of X) t)).f ((m + p) + q) ≫
      (((homotopy f a ha ha1).toSSet.chainComplexMap coeff).hom
        ((m + p) + q) ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q) = 0 := by
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  apply AnnularCollarCut.prism_zero_of_distance m p h hρr hr T hT q
  intro z
  exact ht z.2.down z.1

theorem cycle_boundary
    (h₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (homotopy f a ha ha1 (s, (0, x))) ≤ δ)
    (h₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (homotopy f a ha ha1 (s, (1, x))) ≤ δ) (q : ℕ) :
    (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
      (AnnularTimeTrim.component m p h hρr hr T hT f q -
        AnnularTimeTrim.component m p h hρr hr T hT (trimmedMap f a ha ha1) q) =
      ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        comparison m p h hρr hr T hT f a ha ha1 q) ≫
          (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q := by
  have he := TimeCylinderComparison.cycle_boundary
    ((AnnularTimeTrim.cylinder (TopCat.of X)).toSSet.chainComplexMap coeff)
    ((homotopy f a ha ha1).toSSet.chainComplexMap coeff)
    (m + p) (AnnularCutComparison.cut m p h hρr hr T hT)
    (AnnularCutComparison.cut_boundary m p h hρr hr T hT)
    (side_zero m p h hρr hr T hT f a ha ha1 0 h₀)
    (side_zero m p h hρr hr T hT f a ha ha1 1 h₁) q
  simpa only [AnnularTimeTrim.component, comparison, AnnularTimeTrim.prism, Category.assoc,
    Preadditive.comp_sub, Preadditive.sub_comp, push, chains] using he

theorem homology_eq
    (hf₀ : ∀ x, distance (m + 1) (f (0, x)) ≤ δ)
    (hf₁ : ∀ x, distance (m + 1) (f (1, x)) ≤ δ)
    (ht₀ : ∀ x, distance (m + 1) (trimmedMap f a ha ha1 (0, x)) ≤ δ)
    (ht₁ : ∀ x, distance (m + 1) (trimmedMap f a ha ha1 (1, x)) ≤ δ)
    (h₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (homotopy f a ha ha1 (s, (0, x))) ≤ δ)
    (h₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (homotopy f a ha ha1 (s, (1, x))) ≤ δ) (q : ℕ) :
    (AnnularTrimHomology.operation m p h hρr hr T hT f hf₀ hf₁).homology q =
      (AnnularTrimHomology.operation m p h hρr hr T hT (trimmedMap f a ha ha1) ht₀ ht₁).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (comparison m p h hρr hr T hT f a ha ha1 q)
  exact cycle_boundary m p h hρr hr T hT f a ha ha1 h₀ h₁ q

end
end
end Finsler.CylinderTimeTrim
