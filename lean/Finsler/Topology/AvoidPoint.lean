module

public import Finsler.Analysis.IntervalH1GeodesicCritical
public import Finsler.Geometry.EnergyConservation
public import Finsler.Geometry.PrimeRepresentative
public import Finsler.Geometry.MilnorEquivariance
public import Finsler.Topology.BorelK
public import Finsler.Topology.BorelCrossing
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! A point of the sphere outside countably many smooth closed curves, and the loops avoiding
it. The cone (r, t) ↦ r · γ(t) over a smooth loop is a C¹ map from the plane, so its range has
Hausdorff dimension at most two; for n ≥ 2 the complement of countably many cones is dense in
the ambient space of dimension n + 1, and normalizing a nonzero point of the complement gives a
point of the sphere on none of the loops. If only countably many prime closed geodesic images
exist, some point lies on no closed geodesic. The actual H¹ loops whose whole image avoids a
point form an open set, invariant under reversal and rotation, on which evaluation avoids the
point; under the countability hypothesis it contains every positive-energy tangent-critical
loop. On a reversal-invariant pair of sets of loops avoiding the point, e acts as zero on
reflection Borel cohomology, and if such a pair carries a crossing group (restriction to it is
injective) then e acts as zero on that crossing group. That a neighbourhood of the critical set
carries the crossing group is the local deformation and excision statement, which is separate. -/

@[expose] public section

namespace Finsler.AvoidPoint

open Finsler.SphereGeometry Finsler.Loops Finsler.Geometry Finsler.Geodesics
open Finsler.EnergyConservation Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.SmoothSobolev Finsler.SobolevCurveVariation Finsler.MilnorHomotopy
open Finsler.MilnorEquivariance
open Set Module
open scoped ContDiff

noncomputable section

variable {n : ℕ}

/-- The cone over a smooth loop. -/
def cone (γ : SmoothLoop n) (z : ℝ × ℝ) : Ambient n := z.1 • position γ z.2

theorem cone_contDiff (γ : SmoothLoop n) : ContDiff ℝ 1 (cone γ) :=
  (contDiff_fst.smul ((position_smooth γ).comp contDiff_snd)).of_le (by simp)

theorem dimH_cone_le (γ : SmoothLoop n) : dimH (range (cone γ)) ≤ 2 := by
  have h := Differentiable.dimH_range_le ((cone_contDiff γ).differentiable (by simp))
  have hf : finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hf] at h
  exact_mod_cast h

/-- Countably many smooth loops in a sphere of dimension at least two miss a point. -/
theorem exists_point_not_mem_range {ι : Type*} [Countable ι] (hn : 2 ≤ n)
    (γ : ι → SmoothLoop n) : ∃ p : Sphere n, ∀ i t, γ i t ≠ p := by
  have hdim : dimH (⋃ i, range (cone (γ i))) < finrank ℝ (Ambient n) := by
    rw [dimH_iUnion]
    have h2 : (⨆ i, dimH (range (cone (γ i)))) ≤ 2 := iSup_le fun i => dimH_cone_le (γ i)
    have hf : finrank ℝ (Ambient n) = n + 1 := finrank_euclideanSpace_fin
    rw [hf]
    refine lt_of_le_of_lt h2 ?_
    exact_mod_cast (by omega : 2 < n + 1)
  have hdense := dense_compl_of_dimH_lt_finrank hdim
  obtain ⟨x0, hx0⟩ := (NormedSpace.sphere_nonempty (E := Ambient n)
    (x := (0 : Ambient n))).mpr zero_le_one
  have hx0' : x0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
    exact zero_ne_one hx0
  obtain ⟨x, hx, hxs⟩ := hdense.inter_open_nonempty {x : Ambient n | x ≠ 0} isOpen_ne ⟨x0, hx0'⟩
  have hx' : x ≠ 0 := hx
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
  refine ⟨⟨‖x‖⁻¹ • x, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
  · intro i t hit
    apply hxs
    refine mem_iUnion.mpr ⟨i, (‖x‖, t), ?_⟩
    have hp : position (γ i) t = ‖x‖⁻¹ • x := congrArg Subtype.val hit
    change ‖x‖ • position (γ i) t = x
    rw [hp, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-- If there are only countably many prime closed geodesic images, some point of the sphere lies
on no closed geodesic. -/
theorem exists_point_not_mem_closedGeodesic (F : ReversibleMetric n) (hn : 2 ≤ n)
    (hc : (primeImages F).Countable) :
    ∃ p : Sphere n, ∀ g : ClosedGeodesic F, ∀ t, g.loop t ≠ p := by
  have hcount : Countable (primeImages F) := hc.to_subtype
  have hrep : ∀ s : primeImages F, ∃ g : ClosedGeodesic F, Finsler.Loops.image g.loop = s.1 := by
    intro s
    obtain ⟨g, _, hg⟩ := s.2
    exact ⟨g, hg⟩
  choose γ hγ using hrep
  obtain ⟨p, hp⟩ := exists_point_not_mem_range hn (fun s => (γ s).loop)
  refine ⟨p, fun g t hgt => ?_⟩
  have hmem : Finsler.Loops.image g.loop ∈ primeImages F := by
    rw [← closedImages_eq_primeImages]
    exact ⟨g, rfl⟩
  have hin : p ∈ Finsler.Loops.image (γ ⟨_, hmem⟩).loop := by
    rw [hγ ⟨_, hmem⟩]
    exact ⟨t, hgt⟩
  obtain ⟨t', ht'⟩ := hin
  exact hp ⟨_, hmem⟩ t' ht'

/-- The actual H¹ sphere loops whose whole image avoids a point. -/
def avoid (p : Sphere n) : Set (SphereLoop n) :=
  {u | ∀ t : ClosedInterval, sphereRepresentative u t ≠ p}

theorem representative_sub_le (u v : SphereLoop n) (t : ClosedInterval) :
    ‖(sphereRepresentative v t : Ambient n) - (sphereRepresentative u t : Ambient n)‖ ≤
      2 * dist v u := by
  have he : (sphereRepresentative v t : Ambient n) - (sphereRepresentative u t : Ambient n) =
      traceL n t ((v.data : Space n) - (u.data : Space n)) :=
    (map_sub (traceL n t) (v.data : Space n) (u.data : Space n)).symm
  have hd : dist v u = ‖(v.data : Space n) - (u.data : Space n)‖ :=
    ((sphereLoop_data_isometry n).dist_eq v u).symm.trans
      (dist_eq_norm (v.data : Space n) (u.data : Space n))
  calc ‖(sphereRepresentative v t : Ambient n) - (sphereRepresentative u t : Ambient n)‖
      = ‖traceL n t ((v.data : Space n) - (u.data : Space n))‖ := congrArg norm he
    _ ≤ ‖traceL n t‖ * ‖(v.data : Space n) - (u.data : Space n)‖ := (traceL n t).le_opNorm _
    _ ≤ 2 * ‖(v.data : Space n) - (u.data : Space n)‖ :=
      mul_le_mul_of_nonneg_right (traceL_norm_le n t) (norm_nonneg _)
    _ = 2 * dist v u := by rw [hd]

/-- The loops avoiding a point form an open set in the strong H¹ topology. -/
theorem avoid_isOpen (p : Sphere n) : IsOpen (avoid p) := by
  rw [Metric.isOpen_iff]
  intro u hu
  let f : ClosedInterval → ℝ := fun t => ‖(sphereRepresentative u t : Ambient n) - (p : Ambient n)‖
  have hf : Continuous f :=
    ((continuous_subtype_val.comp (sphereRepresentative_continuous u)).sub continuous_const).norm
  obtain ⟨t0, _, ht0⟩ := isCompact_univ.exists_isMinOn (univ_nonempty (α := ClosedInterval))
    hf.continuousOn
  have hpos : 0 < f t0 := by
    apply norm_pos_iff.mpr
    intro h
    exact hu t0 (Subtype.ext (sub_eq_zero.mp h))
  refine ⟨f t0 / 2, by positivity, ?_⟩
  intro v hv t hvt
  have hmin : f t0 ≤ f t := ht0 (mem_univ t)
  have hle := representative_sub_le u v t
  have hdist : dist v u < f t0 / 2 := hv
  have heq : (sphereRepresentative v t : Ambient n) = (p : Ambient n) := congrArg Subtype.val hvt
  have hft : f t = ‖(sphereRepresentative v t : Ambient n) - (sphereRepresentative u t : Ambient n)‖ := by
    change ‖(sphereRepresentative u t : Ambient n) - (p : Ambient n)‖ = _
    rw [heq, norm_sub_rev]
  linarith

theorem reverse_mem_avoid {p : Sphere n} {u : SphereLoop n} (hu : u ∈ avoid p) :
    reverseSphere u ∈ avoid p := by
  intro t
  rw [sphereRepresentative_reverseSphere]
  exact hu (reflectionInterval t)

theorem eval_ne_of_mem_avoid {p : Sphere n} {u : SphereLoop n} (hu : u ∈ avoid p)
    (t : ClosedInterval) : sphereRepresentative u t ≠ p := hu t

theorem pt_eq_representative (u : SphereLoop n) (t : ClosedInterval) :
    pt u (t : ℝ) = sphereRepresentative u t := Subtype.ext (pt_coe u t.property)

/-- A loop avoiding a point avoids it at every real time. -/
theorem pt_ne_of_mem_avoid {p : Sphere n} {u : SphereLoop n} (hu : u ∈ avoid p) (x : ℝ) :
    pt u x ≠ p := by
  have hfr : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have h := Finsler.BorelK.pt_eq_of_sub_int u (x := Int.fract x) (y := x) ⌊x⌋
    (Int.self_sub_fract x)
  rw [← h]
  exact (pt_eq_representative u ⟨Int.fract x, hfr⟩).trans_ne (hu ⟨Int.fract x, hfr⟩)

/-- The loops avoiding a point are invariant under every rotation of the parameter. -/
theorem vadd_mem_avoid {p : Sphere n} {u : SphereLoop n} (hu : u ∈ avoid p)
    (c : SobolevCircleRepresentative.Circle) : c +ᵥ u ∈ avoid p := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective c
  intro t
  rw [← pt_eq_representative]
  exact (pt_vadd u s (t : ℝ)).trans_ne (pt_ne_of_mem_avoid hu _)

/-- Every positive-energy tangent-critical loop avoids a point lying on no closed geodesic. -/
theorem critical_mem_avoid (F : ReversibleMetric n) {p : Sphere n}
    (hp : ∀ g : ClosedGeodesic F, ∀ t, g.loop t ≠ p) (u : SphereLoop n)
    (hE : 0 < Finsler.SobolevEnergy.energy F u) (hcrit : TangentCritical F u) : u ∈ avoid p := by
  obtain ⟨g, rfl⟩ :=
    (Finsler.SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic F u hE).mp hcrit
  intro t
  rw [sphereRepresentative_ofSmooth]
  exact hp g t

section Pairs

open CategoryTheory SphereOddDegree Finsler.BorelLoop Finsler.BorelPair Finsler.BorelCochain
open Finsler.BorelEvaluation Finsler.SphereTopClass Finsler.BorelCrossing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {s t : Set (Loops n)} (hst : s ⊆ t)
  (hs : ∀ u : SphereLoop n, u ∈ s → reverseSphere u ∈ s)
  (ht : ∀ u : SphereLoop n, u ∈ t → reverseSphere u ∈ t)

/-- The reversal on a reversal-invariant set of loops. -/
def revSet : C(t, t) :=
  ⟨fun u => ⟨reverseSphere (u : SphereLoop n), ht _ u.2⟩,
    ((reverseSphere_continuous n).comp continuous_subtype_val).subtype_mk _⟩

/-- The reversal of a pair of reversal-invariant sets of loops. -/
def revSub : pairOf hst ⟶ pairOf hst :=
  pairMap hst hst (revSet ht) (fun _ hx => hs _ hx)

theorem revSub_sq : revSub hst hs ht ≫ revSub hst hs ht = 𝟙 (pairOf hst) := by
  have h : (revSet ht).comp (revSet ht) = ContinuousMap.id t := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverseSphere_involutive (u : SphereLoop n)) :
      (⟨reverseSphere (reverseSphere (u : SphereLoop n)), ht _ (ht _ u.2)⟩ : t) = u)
  exact (pairMap_comp hst hst hst (revSet ht) (revSet ht) (fun _ hx => hs _ hx)
    (fun _ hx => hs _ hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

/-- Evaluation at zero on a set of loops. -/
def evalSub : (pairOf hst).fst ⟶ sphere n :=
  TopCat.ofHom ⟨fun u => eval n u.val, (eval n).continuous.comp continuous_subtype_val⟩

theorem evalSub_invariant :
    TopPair.Hom.fst (revSub hst hs ht) ≫ evalSub hst = evalSub hst := by
  ext u : 1
  exact eval_reverse u.val

/-- The canonical e action on the reflection Borel cohomology of a pair of sets of loops. -/
def subE (hn : 1 ≤ n) (q : ℕ) :
    HR (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) q →ₗ[ZMod 2]
      HR (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) (n + q) :=
  BorelCup.cup (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht) n
    (cochainPullback (evalSub hst) n (classRepr (sphere n) n (topClass n hn)))
    (cochainPullback_cocycle _ _ _ (classRepr_isCocycle (sphere n) n (topClass n hn)))
    (cochain_invariant _ _ (evalSub_invariant hst hs ht) n _) q

theorem subE_eq_action (hn : 1 ≤ n) (q : ℕ) :
    subE hst hs ht hn q =
      (BorelPullbackCup.classAction (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)
        (evalSub hst) (evalSub_invariant hst hs ht) n q).hom (topClass n hn) := by
  have h := BorelPullbackCup.classAction_mk (pairOf hst) (revSub hst hs ht)
    (revSub_sq hst hs ht) (evalSub hst) (evalSub_invariant hst hs ht) n
    (classRepr (sphere n) n (topClass n hn)) (classRepr_isCocycle (sphere n) n (topClass n hn)) q
  change (BorelPullbackCup.classAction (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)
    (evalSub hst) (evalSub_invariant hst hs ht) n q).hom (cocycleClass (sphere n) n _ _) =
    subE hst hs ht hn q at h
  rw [cocycleClass_classRepr] at h
  exact h.symm

/-- On a pair of sets of loops avoiding a point, e acts as zero on reflection Borel
cohomology. -/
theorem subE_zero_of_subset_avoid (hn : 1 ≤ n) (p : Sphere n) (hp : t ⊆ avoid p) (q : ℕ) :
    subE hst hs ht hn q = 0 := by
  rw [subE_eq_action]
  exact SpherePuncturedEvaluation.classAction_topClass_zero_of_avoids (pairOf hst)
    (revSub hst hs ht) (revSub_sq hst hs ht) n hn p (evalSub hst) (evalSub_invariant hst hs ht)
    (fun x => hp x.2 zero) q

variable (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)
  (hsa : s ⊆ lev F a) (htb : t ⊆ lev F b)

/-- The inclusion of a pair of sets of loops into the crossing pair. -/
def toCross : pairOf hst ⟶ crossPair F hab :=
  pairMap hst (lev_mono F hab) (ContinuousMap.inclusion htb) (fun _ hx => hsa hx)

theorem toCross_equivariant :
    toCross hst F hab hsa htb ≫ revCross F hab = revSub hst hs ht ≫ toCross hst F hab hsa htb := by
  ext : 2 <;> rfl

theorem toCross_eval :
    TopPair.Hom.fst (toCross hst F hab hsa htb) ≫ crossEval F hab = evalSub hst := by
  ext u
  rfl

/-- Restriction of crossing cochains to a pair of sets of loops. -/
abbrev toCrossHom : InvHom (crossComplex F hab)
    (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) :=
  pullHom (revSub_sq hst hs ht) (revCross_sq F hab) (toCross hst F hab hsa htb)
    (toCross_equivariant hst hs ht F hab hsa htb)

/-- Naturality of e for the inclusion of a pair of sets of loops into the crossing pair. -/
theorem crossE_toCross (hn : 1 ≤ n) (q : ℕ) (z : HR (crossComplex F hab) q) :
    HRmap (toCrossHom hst hs ht F hab hsa htb) (n + q) (crossE F hab hn q z) =
      subE hst hs ht hn q (HRmap (toCrossHom hst hs ht F hab hsa htb) q z) := by
  apply BorelCup.cup_natural
  rw [cochain_comp, toCross_eval]

/-- If a reversal-invariant pair of sets of loops avoiding a point carries the crossing group,
in the sense that restriction to it is injective on reflection Borel cohomology in degree
n + q, then e acts as zero on the crossing group in degree q. -/
theorem crossE_zero_of_carrier (hn : 1 ≤ n) (p : Sphere n) (hp : t ⊆ avoid p) (q : ℕ)
    (hinj : Function.Injective (HRmap (toCrossHom hst hs ht F hab hsa htb) (n + q)))
    (z : HR (crossComplex F hab) q) : crossE F hab hn q z = 0 := by
  apply hinj
  rw [crossE_toCross, subE_zero_of_subset_avoid hst hs ht hn p hp q, LinearMap.zero_apply,
    map_zero]

end Pairs

end

end Finsler.AvoidPoint
