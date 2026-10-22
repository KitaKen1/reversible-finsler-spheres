module

public import Finsler.Topology.TameHomology
public import Finsler.Topology.NilpotentW
public import Finsler.Geometry.SphereRetraction

/-! Finite dimensionality at regular finite cuts. For a polygon model, sampling maps the loops
of energy at most a² into a compact set of ambient polygons, and the broken geodesic of the
vertexwise normalization is defined and continuous on an open set of ambient polygons
containing it; the composite is the straightening on the grid, which is homotopic to the
inclusion of sublevels. Between the compact set and the open set there is a finite union of
open balls, whose mod 2 homology is finite dimensional and vanishes in high degrees. Hence, if
the interval [a, b] carries a level deformation, so that the inclusion of t_a into t_b is
injective on homology, the homology of t_a is finite dimensional in every degree and vanishes
in high degrees; the same holds for the constant loops, which are a retract of an open subset
of Euclidean space. By the long exact sequence of the pair and the universal coefficient
isomorphism over F₂, the ordinary relative cohomology of (t_a, M) is finite dimensional in
every degree and vanishes in high degrees. Reflection Borel cohomology is finite dimensional
in every degree when ordinary cohomology is, and vanishes in high degrees when moreover some
power of w vanishes. With finitely many prime closed geodesic images this applies to every
regular cut a > 0: the reflection Borel cohomology of (t_a, M) has finite total dimension, and
the K-Borel cohomology of (t_a, M) is finite dimensional in every degree. -/

@[expose] public section

namespace Finsler.FiniteCut

open CategoryTheory CategoryTheory.Limits Set Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.PolygonModel Finsler.PolygonLoop Finsler.PolygonSampling
open Finsler.PolygonCritical Finsler.SphereRetraction
open Finsler.BorelLoop Finsler.BorelCochain Finsler.BorelPair Finsler.BorelComparison
open Finsler.BorelDeformation Finsler.RegularInterval Finsler.BirkhoffDescent
open Finsler.TameHomology Finsler.RelativeCohomology Finsler.CriticalLevels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Ambient polygons -/

section Model

variable {F : ReversibleMetric n} {b : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F b N)

/-- Vertexwise normalization of an ambient polygon. -/
def nrm (p : ZMod N → Ambient n) : ZMod N → Sphere n := fun i => normalize (p i)

omit [NeZero N] in
theorem nrm_coe (q : ZMod N → Sphere n) : nrm (fun i => (q i : Ambient n)) = q :=
  funext fun i => normalize_inclusion (q i)

omit [NeZero N] in
theorem nrm_continuousOn : ContinuousOn (nrm (n := n) (N := N)) {p | ∀ i, p i ≠ 0} := by
  refine continuousOn_pi.mpr fun i p hp => ?_
  have h1 : ContinuousAt (fun p : ZMod N → Ambient n => p i) p :=
    (continuous_apply i).continuousAt
  have h2 : ContinuousAt (normalize (n := n)) (p i) := (normalize_smoothAt (hp i)).continuousAt
  exact (ContinuousAt.comp (g := normalize (n := n))
    (f := fun p : ZMod N → Ambient n => p i) h2 h1).continuousWithinAt

theorem isOpen_nonzero : IsOpen {p : ZMod N → Ambient n | ∀ i, p i ≠ 0} := by
  have h : {p : ZMod N → Ambient n | ∀ i, p i ≠ 0} =
      ⋂ i, (fun p : ZMod N → Ambient n => p i) ⁻¹' {0}ᶜ := by
    ext p
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_compl_singleton.preimage (continuous_apply i)

open Classical in
/-- The broken geodesic of a polygon; a constant loop if the polygon is not short. -/
def brokenTot (q : ZMod N → Sphere n) : SphereLoop n :=
  if h : ShortPolygon M.δ q then broken M ⟨q, h⟩ else constantSphereLoop (q 0)

theorem brokenTot_of_short {q : ZMod N → Sphere n} (h : ShortPolygon M.δ q) :
    brokenTot M q = broken M ⟨q, h⟩ :=
  dite_eq_left h

theorem brokenTot_continuousOn : ContinuousOn (brokenTot M) {q | ShortPolygon M.δ q} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : ({q : ZMod N → Sphere n | ShortPolygon M.δ q}).domRestrict (brokenTot M) =
      broken M :=
    funext fun q => brokenTot_of_short M q.2
  rw [h]
  exact broken_continuous M

/-- The broken geodesic of the normalization of an ambient polygon. -/
def ambBroken (p : ZMod N → Ambient n) : SphereLoop n := brokenTot M (nrm p)

/-- The ambient polygons with nonzero vertices whose normalization is short. -/
def shortDom : Set (ZMod N → Ambient n) :=
  {p | ∀ i, p i ≠ 0} ∩ nrm ⁻¹' {q | ShortPolygon M.δ q}

theorem shortDom_isOpen : IsOpen (shortDom M) :=
  nrm_continuousOn.isOpen_inter_preimage isOpen_nonzero (shortPolygon_isOpen M.δ N)

theorem ambBroken_continuousOn : ContinuousOn (ambBroken M) (shortDom M) :=
  (brokenTot_continuousOn M).comp (nrm_continuousOn.mono inter_subset_left) fun _ hp => hp.2

/-- The open set of ambient polygons whose broken geodesic has energy below c². -/
def dom (c : ℝ) : Set (ZMod N → Ambient n) :=
  shortDom M ∩ (fun p => energy F (ambBroken M p)) ⁻¹' Iio (c ^ 2)

theorem dom_isOpen (c : ℝ) : IsOpen (dom M c) :=
  ((Finsler.SobolevEnergy.energy_continuous F).comp_continuousOn
    (ambBroken_continuousOn M)).isOpen_inter_preimage
    (shortDom_isOpen M) isOpen_Iio

/-- The ambient polygon of the samples of a loop. -/
def sampleAmb (u : SphereLoop n) : ZMod N → Ambient n := fun i => (samplePoly N u i : Ambient n)

omit [NeZero N] in
theorem sampleAmb_continuous : Continuous (sampleAmb (n := n) (N := N)) :=
  continuous_pi fun i =>
    continuous_subtype_val.comp ((continuous_apply i).comp (samplePoly_continuous N))

omit [NeZero N] in
theorem nrm_sampleAmb (u : SphereLoop n) : nrm (sampleAmb (N := N) u) = samplePoly N u :=
  nrm_coe _

/-- The broken geodesic of the samples of a loop of the model is the straightening on the
grid. -/
theorem ambBroken_sampleAmb {u : SphereLoop n} (hu : energy F u < b ^ 2) :
    ambBroken M (sampleAmb u) = deform M (1, u) := by
  rw [ambBroken, nrm_sampleAmb, brokenTot_of_short M (sample_short M hu), deform_one M hu]

/-- The set of the short polygons whose broken geodesic has energy at most c², in the ambient
space. -/
def cpt (c : ℝ) : Set (ZMod N → Ambient n) :=
  (fun q : {q : ZMod N → Sphere n // ShortPolygon M.δ q} => fun i => (q.1 i : Ambient n)) ''
    band M 0 (c ^ 2)

theorem cpt_isCompact (c : ℝ)
    (hedge : ∀ q : ZMod N → Sphere n, polyEnergy F N (fun i => (q i : Ambient n)) ≤ c ^ 2 →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2) : IsCompact (cpt M c) :=
  (band_isCompact M 0 (c ^ 2) hedge).image
    (continuous_pi fun i =>
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val))

theorem cpt_subset_dom {c c' : ℝ} (hc : c ^ 2 < c' ^ 2) : cpt M c ⊆ dom M c' := by
  rintro _ ⟨q, hq, rfl⟩
  have hn : nrm (fun i => (q.1 i : Ambient n)) = q.1 := nrm_coe q.1
  refine ⟨⟨fun i => ne_zero_of_mem_unit_sphere (q.1 i), ?_⟩, ?_⟩
  · change ShortPolygon M.δ (nrm fun i => (q.1 i : Ambient n))
    rw [hn]
    exact q.2
  · change energy F (brokenTot M (nrm fun i => (q.1 i : Ambient n))) < c' ^ 2
    rw [hn, brokenTot_of_short M q.2]
    exact lt_of_le_of_lt hq.2 hc

theorem sampleAmb_mem_cpt {c : ℝ} {u : SphereLoop n} (hub : energy F u < b ^ 2)
    (huc : energy F u ≤ c ^ 2) : sampleAmb u ∈ cpt M c := by
  refine ⟨⟨samplePoly N u, sample_short M hub⟩, ⟨energy_nonneg F _, ?_⟩, rfl⟩
  rw [energy_broken]
  exact (polyEnergy_samplePoly_le u).trans huc

/-- If [a, b] carries a level deformation, the sublevel t_a is tame: its mod 2 homology is
finite dimensional in every degree and vanishes in high degrees. -/
theorem tame_lev_of_model (hb : 0 < b) {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hedge : ∀ q : ZMod N → Sphere n, polyEnergy F N (fun i => (q i : Ambient n)) ≤ a ^ 2 →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2)
    (D : LevelDeformation F a b b) : ∃ k : ℕ, Tame (TopCat.of ↥(lev F a)) k := by
  have hc : a ^ 2 < b ^ 2 := pow_lt_pow_left₀ hab ha.le two_ne_zero
  obtain ⟨Q, m, -, hKQ, hQΩ, hQ⟩ := exists_tame_between (cpt_isCompact M a hedge)
    (dom_isOpen M b) (cpt_subset_dom M hc)
  have hxa : ∀ x : lev F a, energy F (x : SphereLoop n) < a ^ 2 := fun x =>
    (Birkhoff.mem_lev_iff ha _).mp x.2
  let f : C(lev F a, Q) :=
    ⟨fun x => ⟨sampleAmb (x : SphereLoop n),
        hKQ (sampleAmb_mem_cpt M ((hxa x).trans hc) (hxa x).le)⟩,
      (sampleAmb_continuous.comp continuous_subtype_val).subtype_mk _⟩
  let g : C(Q, lev F b) :=
    ⟨fun p => ⟨ambBroken M (p : ZMod N → Ambient n),
        (Birkhoff.mem_lev_iff hb _).mpr (hQΩ p.2).2⟩,
      ((ambBroken_continuousOn M).comp_continuous continuous_subtype_val
        fun p => (hQΩ p.2).1).subtype_mk _⟩
  have hgf : g.comp f =
      (Birkhoff.d1 M hb).comp (ContinuousMap.inclusion (lev_mono F hab.le)) := by
    ext x
    exact ambBroken_sampleAmb M ((hxa x).trans hc)
  have H₁ := (Birkhoff.g1 M hb).compContinuousMap
    (ContinuousMap.inclusion (lev_mono F hab.le))
  have hH : TopCat.Homotopy (TopCat.ofHom f ≫ TopCat.ofHom g)
      (TopCat.ofHom (ContinuousMap.inclusion (lev_mono F hab.le))) := by
    change ContinuousMap.Homotopy (g.comp f) (ContinuousMap.inclusion (lev_mono F hab.le))
    rw [hgf]
    exact H₁.symm
  refine ⟨m, tame_of_factor (TopCat.ofHom f) (TopCat.ofHom g) hQ fun q => ?_⟩
  rw [HqMap_congr hH]
  exact injective_of_leftInverse (TopCat.ofHom (ContinuousMap.inclusion (lev_mono F hab.le)))
    (TopCat.ofHom (endMap (toPair (toDeformationConsts D))))
    (homT (lev_mono F hab.le) (toPair (toDeformationConsts D))) q

end Model

/-- If [a, b] carries a level deformation, the sublevel t_a is tame. -/
theorem tame_lev (F : ReversibleMetric n) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (D : LevelDeformation F a b b) : ∃ k : ℕ, Tame (TopCat.of ↥(lev F a)) k := by
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S₀.δ) (a := b) S₀.pos
  obtain ⟨N₁, hN₁⟩ := exists_edge_bound F hn a (S₀.δ / 2) (half_pos S₀.pos)
  have hN0 : N₀ ≤ max N₀ N₁ + 1 := (le_max_left N₀ N₁).trans (Nat.le_succ _)
  have hN1 : N₁ ≤ max N₀ N₁ + 1 := (le_max_right N₀ N₁).trans (Nat.le_succ _)
  let M : PolygonModelData F b (max N₀ N₁ + 1) :=
    PolygonModelData.mk S₀ fun u hu s t hs ht hst =>
      hN₀ (max N₀ N₁ + 1) hN0 (Nat.succ_pos _) u hu s t hs ht hst
  exact tame_lev_of_model M (ha.trans hab) ha hab
    (fun q hq i => hN₁ (max N₀ N₁ + 1) hN1 q hq i) D

/-- The constant loops are tame. -/
theorem tame_consts (n : ℕ) : ∃ k : ℕ, Tame (TopCat.of ↥(consts n)) k := by
  have hK : IsCompact (Metric.sphere (0 : Ambient n) 1) := isCompact_sphere 0 1
  have hΩ : IsOpen ({0}ᶜ : Set (Ambient n)) := isOpen_compl_singleton
  have hKΩ : Metric.sphere (0 : Ambient n) 1 ⊆ {0}ᶜ := fun v hv h0 => by
    rw [mem_singleton_iff.mp h0, mem_sphere_zero_iff_norm, norm_zero] at hv
    exact zero_ne_one hv
  obtain ⟨Q, m, -, hKQ, hQΩ, hQ⟩ := exists_tame_between hK hΩ hKΩ
  let f : C(consts n, Q) :=
    ⟨fun x => ⟨(samplePoly 1 (x : SphereLoop n) 0 : Ambient n), hKQ (samplePoly 1 _ 0).2⟩,
      (continuous_subtype_val.comp ((continuous_apply (0 : ZMod 1)).comp
        ((samplePoly_continuous 1).comp continuous_subtype_val))).subtype_mk _⟩
  have hnorm : ContinuousOn (normalize (n := n)) ({0}ᶜ : Set (Ambient n)) := fun v hv =>
    (normalize_smoothAt hv).continuousAt.continuousWithinAt
  let g : C(Q, consts n) :=
    ⟨fun v => ⟨constantSphereLoop (normalize (v : Ambient n)), mem_range_self _⟩,
      ((Finsler.SphereTopClass.constantSphereLoop_continuous n).comp
        (hnorm.comp_continuous continuous_subtype_val fun v => hQΩ v.2)).subtype_mk _⟩
  have hgf : g.comp f = ContinuousMap.id (consts n) := by
    ext x
    obtain ⟨y, hy⟩ := x.2
    change constantSphereLoop (normalize (samplePoly 1 (x : SphereLoop n) 0 : Ambient n)) =
      (x : SphereLoop n)
    rw [normalize_inclusion, ← hy]
    exact congrArg constantSphereLoop (sphereRepresentative_constantSphereLoop y _)
  refine ⟨m, tame_of_factor (TopCat.ofHom f) (TopCat.ofHom g) hQ fun q => ?_⟩
  have h1 : TopCat.ofHom f ≫ TopCat.ofHom g = 𝟙 (TopCat.of ↥(consts n)) :=
    congrArg TopCat.ofHom hgf
  rw [h1, HqMap_id]
  exact fun x y h => h

/-! ### Ordinary cohomology of a finite cut -/

/-- If [a, b] carries a level deformation, the relative mod 2 homology of (t_a, M) is finite
dimensional in every degree and vanishes in high degrees. -/
theorem exists_levPair_homology (F : ReversibleMetric n) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (D : LevelDeformation F a b b) :
    ∃ k : ℕ, (∀ q, Module.Finite (ZMod 2) (Hrel (levPair F a) q)) ∧
      ∀ q, k ≤ q → IsZero (Hrel (levPair F a) q) := by
  obtain ⟨k₁, h₁⟩ := tame_lev F hn ha hab D
  obtain ⟨k₂, h₂⟩ := tame_consts n
  refine ⟨max k₁ k₂ + 1, fun q => ?_, fun q hq => ?_⟩
  · cases q with
    | zero =>
      have h : Module.Finite (ZMod 2) (Hq (levPair F a).fst 0) := h₁.finite 0
      exact finite_rel_zero _ h
    | succ q =>
      have h : Module.Finite (ZMod 2) (Hq (levPair F a).fst (q + 1)) := h₁.finite (q + 1)
      have h' : Module.Finite (ZMod 2) (Hq (levPair F a).snd q) := h₂.finite q
      exact finite_rel_succ _ q h h'
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h : IsZero (Hq (levPair F a).fst (q' + 1)) :=
      h₁.zero _ (by have := le_max_left k₁ k₂; omega)
    have h' : IsZero (Hq (levPair F a).snd q') :=
      h₂.zero _ (by have := le_max_right k₁ k₂; omega)
    exact isZero_rel_succ _ q' h h'

/-- The ordinary relative cohomology of (t_a, M) is the dual of the relative homology. -/
def dualEquiv (F : ReversibleMetric n) (a : ℝ) (q : ℕ) :
    H (levComplex F a) q ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Hrel (levPair F a) q) :=
  (ordinaryEquiv (levPair F a) (revPair F a) (revPair_sq F a) q).trans
    (RelativeKronecker.equiv (levPair F a) q)

/-- If [a, b] carries a level deformation, the ordinary relative cohomology of (t_a, M) is
finite dimensional in every degree and vanishes in high degrees. -/
theorem exists_H_lev (F : ReversibleMetric n) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (D : LevelDeformation F a b b) :
    ∃ k : ℕ, (∀ q, Module.Finite (ZMod 2) (H (levComplex F a) q)) ∧
      ∀ q, k ≤ q → ∀ x : H (levComplex F a) q, x = 0 := by
  obtain ⟨k, hfin, hzero⟩ := exists_levPair_homology F hn ha hab D
  refine ⟨k, fun q => ?_, fun q hq x => ?_⟩
  · have := hfin q
    exact Module.Finite.equiv (dualEquiv F a q).symm
  · have : Subsingleton (Hrel (levPair F a) q) := ModuleCat.subsingleton_of_isZero (hzero q hq)
    apply (dualEquiv F a q).injective
    apply LinearMap.ext
    intro v
    rw [Subsingleton.elim v 0, map_zero, map_zero]

/-! ### Reflection Borel cohomology -/

section Algebra

variable (K : InvComplex)

/-- Reflection Borel cohomology is finite dimensional in every degree if ordinary cohomology
is. -/
theorem finite_HR (h : ∀ q, Module.Finite (ZMod 2) (H K q)) (q : ℕ) :
    Module.Finite (ZMod 2) (HR K q) := by
  induction q with
  | zero =>
    have := h 0
    exact Module.Finite.of_injective (forget K 0) (BorelQuasiIso.forget_zero_injective K)
  | succ q ih =>
    have := ih
    have := h (q + 1)
    exact finite_of_exact_linear (w K q) (forget K (q + 1))
      fun x hx => (exact_forget K q x).mp hx

/-- Above the degrees in which ordinary cohomology vanishes, every Borel class is a power of w
applied to a class of lower degree. -/
theorem exists_wPow_preimage {Q₁ : ℕ} (hzero : ∀ q, Q₁ ≤ q → ∀ z : H K q, z = 0) (lo : ℕ)
    (hlo : Q₁ ≤ lo + 1) (k : ℕ) (x : HR K (lo + k)) :
    ∃ y : HR K lo, NilpotentW.wPow K lo k y = x := by
  induction k with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
    obtain ⟨y', hy'⟩ := (exact_forget K (lo + k) x).mp (hzero _ (by omega) _)
    obtain ⟨y, hy⟩ := ih y'
    exact ⟨y, by rw [NilpotentW.wPow_succ, hy, hy']⟩

/-- If ordinary cohomology vanishes from degree Q₁ on and the k-th power of w vanishes,
reflection Borel cohomology vanishes from degree Q₁ + k on. -/
theorem HR_eq_zero_of_nilpotent {Q₁ k : ℕ} (hzero : ∀ q, Q₁ ≤ q → ∀ z : H K q, z = 0)
    (hnil : ∀ (lo : ℕ) (x : HR K lo), NilpotentW.wPow K lo k x = 0) (q : ℕ) (hq : Q₁ + k ≤ q)
    (x : HR K q) : x = 0 := by
  obtain ⟨lo, rfl⟩ : ∃ lo, q = lo + k := ⟨q - k, by omega⟩
  obtain ⟨y, rfl⟩ := exists_wPow_preimage K hzero lo (by omega) k x
  exact hnil lo y

end Algebra

/-! ### Regular cuts -/

/-- With finitely many prime closed geodesic images, a regular cut is the lower end of an
interval without critical levels. -/
theorem exists_regular_above (F : ReversibleMetric n) (hfin : (primeImages F).Finite) {a : ℝ}
    (hac : a ∉ crit F) : ∃ b : ℝ, a < b ∧ ∀ x ∈ Icc a b, x ∉ crit F := by
  have hS : (crit F ∩ Icc a (a + 1)).Finite := crit_finite F hfin a (a + 1)
  have ha : a ∈ (crit F ∩ Icc a (a + 1))ᶜ := fun h => hac h.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl a ha
  refine ⟨a + min ε 1 / 2, by have := lt_min hε one_pos; linarith, fun x hx hxc => ?_⟩
  have h1 : min ε 1 ≤ ε := min_le_left _ _
  have h2 : min ε 1 ≤ 1 := min_le_right _ _
  have h3 : 0 < min ε 1 := lt_min hε one_pos
  have hxball : x ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact hball hxball ⟨hxc, hx.1, by linarith [hx.2]⟩

/-- With finitely many prime closed geodesic images, the ordinary relative cohomology of
(t_a, M) at a regular cut a > 0 is finite dimensional in every degree and vanishes in high
degrees. -/
theorem exists_finite_H (F : ReversibleMetric n) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {a : ℝ} (ha : 0 < a) (hac : a ∉ crit F) :
    ∃ k : ℕ, (∀ q, Module.Finite (ZMod 2) (H (levComplex F a) q)) ∧
      ∀ q, k ≤ q → ∀ x : H (levComplex F a) q, x = 0 := by
  obtain ⟨b, hab, hreg⟩ := exists_regular_above F hfin hac
  obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn a b b ha hab.le le_rfl hreg
  exact exists_H_lev F hn ha hab D

/-- With finitely many prime closed geodesic images, the reflection Borel cohomology of
(t_a, M) at a regular cut a > 0 is finite dimensional in every degree and vanishes in high
degrees: its total dimension is finite. -/
theorem exists_finite_HR (F : ReversibleMetric n) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {a : ℝ} (ha : 0 < a) (hac : a ∉ crit F) :
    ∃ k : ℕ, (∀ q, Module.Finite (ZMod 2) (HR (levComplex F a) q)) ∧
      ∀ q, k ≤ q → ∀ x : HR (levComplex F a) q, x = 0 := by
  obtain ⟨Q₁, hfinH, hzero⟩ := exists_finite_H F hn hfin ha hac
  obtain ⟨k, hk⟩ := Finsler.NilpotentW.exists_w_nilpotent F hn hfin a ha hac
  exact ⟨Q₁ + k, finite_HR (levComplex F a) hfinH,
    fun q hq x => HR_eq_zero_of_nilpotent (levComplex F a) hzero hk q hq x⟩

/-- With finitely many prime closed geodesic images, the K-Borel cohomology of (t_a, M) at a
regular cut a > 0 is finite dimensional in every degree. -/
theorem finite_HK (F : ReversibleMetric n) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {a : ℝ} (ha : 0 < a) (hac : a ∉ crit F) (q : ℕ) :
    Module.Finite (ZMod 2) (Finsler.BorelK.HK F a q) := by
  obtain ⟨k, hfinR, -⟩ := exists_finite_HR F hn hfin ha hac
  refine finite_HR (Finsler.BorelK.kComplex F a) (fun j => ?_) q
  have := hfinR j
  exact Module.Finite.equiv (Finsler.BorelK.forgetTargetEquiv F a j).symm

end

end Finsler.FiniteCut
