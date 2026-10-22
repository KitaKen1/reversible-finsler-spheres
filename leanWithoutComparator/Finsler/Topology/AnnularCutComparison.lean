module

public import Finsler.Topology.AnnularSupportedCut
public import Finsler.Topology.TimePrismComparison
public import Finsler.Topology.PrismSelfCut
public import Finsler.Topology.SupportedCapRepresentative

/-! The annular representative gives the same actual tested self-cut on
loop homology, including output degree zero. The comparison uses a primitive
supported off the far set and vanishing at both time endpoints. -/

@[expose] public section
namespace Finsler.AnnularCutComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem primitive_supported (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) (n - 1)
      (AnnularSelfCut.primitive n hn h hρ2) = 0 := by
  let f := SupportedCap.subspaceMap (parameters n) (exterior n ρ) ≫ selfEvaluation n
  let g : TopCat.of (exterior n ρ) ⟶ TopCat.of (DiagonalAvoidanceCocycle.avoid n ρ) :=
    TopCat.ofHom ⟨fun z => ⟨f z, mem_iUnion.mpr ⟨false, by
      change ρ ≤ distance n z.val
      exact z.property.le⟩⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ DiagonalAvoidanceCocycle.inclusion n ρ := by ext z : 1; rfl
  rw [AnnularSelfCut.primitive, ← pullback_comp]
  change cochainPullback f (n - 1) _ = 0
  rw [he, pullback_comp, AnnularThomComparison.ambientPrimitive_supported]
  simp only [cochainPullback, map_zero]

variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def cut (q : ℕ) :
    (chains (parameters (m + 1))).X ((m + p) + q + 1) ⟶
      (chains (TopCat.of (SphereLoop (m + 1)))).X q :=
  SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
    (m + 1) (p + q) ((m + p) + q + 1) (by omega)
    (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) ≫
      (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q

theorem old_cut_explicit (q : ℕ) :
    PrismSelfCut.cut m p (h.1.trans h.2.2) hρr hr T hT q =
      SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        (m + 1) (p + q) ((m + p) + q + 1) (by omega)
        (NormalizedSelfCut.cocycle (m + 1) (by omega) (h.1.trans h.2.2))
        (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) (h.1.trans h.2.2)) ≫
          (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q := by
  have aux (N : ℕ) (he : N = (m + 1) + (p + q)) :
      eqToHom (congrArg (chains (parameters (m + 1))).X he) ≫
        NormalizedSelfCut.chainCut (m + 1) p (by omega) (h.1.trans h.2.2) hρr hr T hT q =
      SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        (m + 1) (p + q) N he.symm
        (NormalizedSelfCut.cocycle (m + 1) (by omega) (h.1.trans h.2.2))
        (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) (h.1.trans h.2.2)) ≫
          (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q := by
    subst N
    rw [eqToHom_refl, Category.id_comp]
    rfl
  exact aux _ (by omega)

theorem cut_boundary (q : ℕ) :
    cut m p h hρr hr T hT (q + 1) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q =
      (chains (parameters (m + 1))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
        cut m p h hρr hr T hT q := by
  have hc := SupportedCap.cut_boundary (parameters (m + 1)) (exterior (m + 1) ρ)
    (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
    (m + 1) (p + q) ((m + p) + q + 1) (by omega)
    (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
    (AnnularSelfCut.cocycle_closed (m + 1) (by omega) h)
  have hc' : SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ)
      (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
      (m + 1) (p + (q + 1)) ((m + p) + (q + 1) + 1) (by omega)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) ≫
      (chains (TopCat.of (neighborhood (m + 1) r))).d (p + (q + 1)) (p + q) =
    (chains (parameters (m + 1))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
      SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ)
        (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        (m + 1) (p + q) ((m + p) + q + 1) (by omega)
        (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) := hc
  unfold cut
  rw [Category.assoc, (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).comm,
    ← Category.assoc]
  rw [hc', Category.assoc]

theorem cut_atTime_zero (q : ℕ) (t : ClosedInterval)
    (ht : cochainPullback (atTime (m + 1) t) (m + 1)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h) = 0) :
    (push (atTime (m + 1) t)).f ((m + p) + q + 1) ≫ cut m p h hρr hr T hT q = 0 := by
  have hs : cochainPullback (SupportedCap.subspaceMap (parameters (m + 1))
      (SelfCutEndpoints.timeSlice (m + 1) t)) (m + 1)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h) = 0 := by
    rw [SelfCutEndpoints.slice_factor, pullback_comp, ht]
    simp only [cochainPullback, map_zero]
  have aux (N : ℕ) (he : N = (m + 1) + (p + q)) :
      (push (atTime (m + 1) t)).f N ≫
        SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
          (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
          (m + 1) (p + q) N he.symm
          (AnnularSelfCut.cocycle (m + 1) (by omega) h)
          (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) = 0 := by
    subst N
    exact SelfCutEndpoints.cut_map_zero _ _ (SelfCutEndpoints.timeSlice (m + 1) t)
      (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) (m + 1) (p + q)
      _ _ hs (atTime (m + 1) t) (fun _ => rfl)
  unfold cut
  rw [← Category.assoc, aux _ (by omega), zero_comp]

theorem cut_time_zero (q : ℕ) :
    (push (atTime (m + 1) 0)).f ((m + p) + q + 1) ≫ cut m p h hρr hr T hT q = 0 :=
  cut_atTime_zero m p h hρr hr T hT q 0 (AnnularSupportedCut.time_zero _ (by omega) h)

theorem cut_time_one (q : ℕ) :
    (push (atTime (m + 1) 1)).f ((m + p) + q + 1) ≫ cut m p h hρr hr T hT q = 0 :=
  cut_atTime_zero m p h hρr hr T hT q 1 (AnnularSupportedCut.time_one _ (by omega) h)

def operation : DegreeLoweringHomology.Map
    (chains (TopCat.of (SphereLoop (m + 1))))
    (chains (TopCat.of (SphereLoop (m + 1)))) (m + p) :=
  TimePrismDescent.operation (SelfCutTimePrism.chainHomotopy (m + 1)) (m + p)
    (cut m p h hρr hr T hT) (cut_boundary m p h hρr hr T hT)
    (cut_time_zero m p h hρr hr T hT) (cut_time_one m p h hρr hr T hT)

variable (hm : 1 ≤ m)

def correction (q : ℕ) :
    (chains (parameters (m + 1))).X ((m + p) + q) ⟶
      (chains (TopCat.of (SphereLoop (m + 1)))).X q :=
  SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
    m (p + q) ((m + p) + q) (by omega)
    (AnnularSelfCut.primitive (m + 1) (by omega) h (by linarith))
    (primitive_supported (m + 1) (by omega) h (by linarith)) ≫
      (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q

theorem correction_boundary (q : ℕ) :
    correction m p h hρr hr T hT hm (q + 1) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q =
      (chains (parameters (m + 1))).d ((m + p) + q + 1) ((m + p) + q) ≫
        correction m p h hρr hr T hT hm q -
        (cut m p h hρr hr T hT q - PrismSelfCut.cut m p (h.1.trans h.2.2) hρr hr T hT q) := by
  let κ := AnnularSelfCut.primitive (m + 1) (by omega : 2 ≤ m + 1) h (by linarith : ρ ≤ 2)
  have hs : cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (exterior (m + 1) ρ)) m κ = 0 :=
    primitive_supported (m + 1) (by omega) h (by linarith)
  have he : cochainCoboundary (ZMod 2) (parameters (m + 1)) m κ =
      AnnularSelfCut.cocycle (m + 1) (by omega) h -
        NormalizedSelfCut.cocycle (m + 1) (by omega) (h.1.trans h.2.2) :=
    AnnularSelfCut.primitive_boundary (m + 1) (by omega) h (by linarith)
  have hdiff := SupportedCapRepresentative.support_sub (parameters (m + 1)) (exterior (m + 1) ρ)
    (m + 1) _ _ (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) (h.1.trans h.2.2))
  have hd : cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (exterior (m + 1) ρ))
      (m + 1) (cochainCoboundary (ZMod 2) (parameters (m + 1)) m κ) = 0 := by
    rw [he]
    exact hdiff
  have hc := SupportedCapCochain.cut_coboundary (parameters (m + 1)) (exterior (m + 1) ρ)
    (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
    m (p + q) ((m + p) + q) (by omega) κ hs hd
  have hcs := (SupportedCapRepresentative.cut_congr (parameters (m + 1))
    (exterior (m + 1) ρ) (neighborhood (m + 1) r) (exterior_open _ _)
    (neighborhood_open _ _) (cover _ hρr) (m + 1) (p + q) ((m + p) + q + 1)
    (by omega) _ _ hd hdiff he).trans
      (SupportedCapCochain.cut_sub (parameters (m + 1)) (exterior (m + 1) ρ)
        (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        (m + 1) (p + q) ((m + p) + q + 1) (by omega) _ _
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) (h.1.trans h.2.2)) hdiff)
  have hc' : SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ)
      (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
      m (p + (q + 1)) ((m + p) + (q + 1)) (by omega) κ hs ≫
      (chains (TopCat.of (neighborhood (m + 1) r))).d (p + (q + 1)) (p + q) =
    (chains (parameters (m + 1))).d ((m + p) + q + 1) ((m + p) + q) ≫
      SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ)
        (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        m (p + q) ((m + p) + q) (by omega) κ hs -
      SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ)
        (neighborhood (m + 1) r) (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        (m + 1) (p + q) ((m + p) + q + 1) (by omega)
        (cochainCoboundary (ZMod 2) (parameters (m + 1)) m κ) hd := hc
  rw [old_cut_explicit m p h hρr hr T hT q]
  unfold correction cut
  rw [Category.assoc, (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).comm,
    ← Category.assoc]
  rw [hc', hcs]
  simp only [Preadditive.sub_comp, Category.assoc, κ]

theorem correction_atTime_zero (q : ℕ) (t : ClosedInterval)
    (ht : cochainPullback (atTime (m + 1) t) m
      (AnnularSelfCut.primitive (m + 1) (by omega) h (by linarith)) = 0) :
    (push (atTime (m + 1) t)).f ((m + p) + q) ≫ correction m p h hρr hr T hT hm q = 0 := by
  have hs : cochainPullback (SupportedCap.subspaceMap (parameters (m + 1))
      (SelfCutEndpoints.timeSlice (m + 1) t)) m
      (AnnularSelfCut.primitive (m + 1) (by omega) h (by linarith)) = 0 := by
    rw [SelfCutEndpoints.slice_factor, pullback_comp, ht]
    simp only [cochainPullback, map_zero]
  have aux (N : ℕ) (he : N = m + (p + q)) :
      (push (atTime (m + 1) t)).f N ≫
        SupportedCap.cut (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
          (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m (p + q) N he.symm
          (AnnularSelfCut.primitive (m + 1) (by omega) h (by linarith))
          (primitive_supported (m + 1) (by omega) h (by linarith)) = 0 := by
    subst N
    exact SelfCutEndpoints.cut_map_zero _ _ (SelfCutEndpoints.timeSlice (m + 1) t)
      (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m (p + q)
      _ _ hs (atTime (m + 1) t) (fun _ => rfl)
  unfold correction
  rw [← Category.assoc, aux _ (by omega), zero_comp]

theorem correction_time_zero (q : ℕ) :
    (push (atTime (m + 1) 0)).f ((m + p) + q) ≫ correction m p h hρr hr T hT hm q = 0 :=
  correction_atTime_zero m p h hρr hr T hT hm q 0
    (AnnularSelfCut.primitive_time_zero (m + 1) (by omega) h (by linarith))

theorem correction_time_one (q : ℕ) :
    (push (atTime (m + 1) 1)).f ((m + p) + q) ≫ correction m p h hρr hr T hT hm q = 0 :=
  correction_atTime_zero m p h hρr hr T hT hm q 1
    (AnnularSelfCut.primitive_time_one (m + 1) (by omega) h (by linarith))

include hm in
theorem operation_homology_eq (q : ℕ) :
    (operation m p h hρr hr T hT).homology q =
      (PrismSelfCut.operation m p (h.1.trans h.2.2) hρr hr T hT).homology q := by
  apply TimePrismComparison.homology_eq (SelfCutTimePrism.chainHomotopy (m + 1)) (m + p)
    (cut m p h hρr hr T hT) (PrismSelfCut.cut m p (h.1.trans h.2.2) hρr hr T hT)
    (correction m p h hρr hr T hT hm)
    (correction_boundary m p h hρr hr T hT hm)
    (correction_time_zero m p h hρr hr T hT hm)
    (correction_time_one m p h hρr hr T hT hm)
    (operation m p h hρr hr T hT) (PrismSelfCut.operation m p (h.1.trans h.2.2) hρr hr T hT)
    (fun _ => rfl) (fun _ => rfl) q

end
end Finsler.AnnularCutComparison
