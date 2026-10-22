module
public import Finsler.Topology.BorelEvaluationClass
public import Finsler.Topology.Kronecker
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
/-! The unique nonzero mod-two top class of the actual Euclidean sphere, obtained from the pinned Tau Ceti sphere homology and the actual Kronecker isomorphism. A continuous constant-loop section proves ordinary ambient evaluation pullback injective on the full pair and every cut, hence the canonical ordinary e is nonzero. Positive-degree cohomology outside the sphere dimension vanishes, so the top class has square zero. This does not identify the ordinary e with an element of geometric equivariant cohomology. -/

@[expose] public section
namespace Finsler.SphereTopClass
open CategoryTheory SphereOddDegree Finsler.BorelEvaluation
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def homologyIso (n : ℕ) (hn : 1≤n) :
    homologyZMod2 (sphere n) n ≅ ModuleCat.of (ZMod 2) (ZMod 2) := by
  cases n with
  | zero => omega
  | succ m =>
    have h : Module.finrank ℝ (Finsler.SphereGeometry.Ambient (m+1)) = (m+1)+1 :=
      (Finsler.SphereGeometry.ambientDimension (m+1)).out
    exact ((TauCeti.reducedSingularHomologySuccIso (ModuleCat.of (ZMod 2) (ZMod 2)) m).app
      (sphere (m+1))).symm ≪≫
      TauCeti.reducedSingularHomologySphereIso (ModuleCat.of (ZMod 2) (ZMod 2)) h

def homologyEquiv (n : ℕ) (hn : 1≤n) : homologyZMod2 (sphere n) n ≃ₗ[ZMod 2] ZMod 2 :=
  (homologyIso n hn).toLinearEquiv

/-- Identify the dual of the one-dimensional actual top homology with F₂ by evaluation at its generator. -/
def dualEquiv (n : ℕ) (hn : 1≤n) :
    (homologyZMod2 (sphere n) n →ₗ[ZMod 2] ZMod 2) ≃ₗ[ZMod 2] ZMod 2 where
  toFun g := g ((homologyEquiv n hn).symm 1)
  invFun a := a • (homologyEquiv n hn).toLinearMap
  left_inv g := by
    ext z
    let e := homologyEquiv n hn
    have hz : z = (e z) • e.symm 1 := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
    change g (e.symm 1) • e z = g z
    calc
      _ = (e z) • g (e.symm 1) := by exact mul_comm _ _
      _ = g ((e z) • e.symm 1) := (map_smul g (e z) (e.symm 1)).symm
      _ = g z := congrArg g hz.symm
  right_inv a := by
    change a • (homologyEquiv n hn) ((homologyEquiv n hn).symm 1)=a
    rw [LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cohomologyEquiv (n : ℕ) (hn : 1≤n) : cohomologyZMod2 (sphere n) n ≃ₗ[ZMod 2] ZMod 2 :=
  (kroneckerEquiv (sphere n) n).toLinearEquiv.trans (dualEquiv n hn)

/-- The canonical mod-two top cohomology class, characterized below as the unique nonzero element. -/
def topClass (n : ℕ) (hn : 1≤n) : cohomologyZMod2 (sphere n) n := (cohomologyEquiv n hn).symm 1

theorem topClass_ne_zero (n : ℕ) (hn : 1≤n) : topClass n hn≠0 := by
  intro h
  apply (one_ne_zero : (1 : ZMod 2)≠0)
  calc
    1 = cohomologyEquiv n hn (topClass n hn) := (LinearEquiv.apply_symm_apply _ _).symm
    _ = cohomologyEquiv n hn 0 := congrArg (cohomologyEquiv n hn) h
    _ = 0 := map_zero _

theorem eq_topClass_of_ne_zero (n : ℕ) (hn : 1≤n) (a : cohomologyZMod2 (sphere n) n)
    (ha : a≠0) : a=topClass n hn := by
  let e := cohomologyEquiv n hn
  have hc : e a≠0 := by
    intro h
    apply ha
    apply e.injective
    simpa only [map_zero] using h
  have h01 : ∀ z : ZMod 2, z=0 ∨ z=1 := by
    intro z
    fin_cases z <;> simp
  have h1 : e a=1 := (h01 (e a)).resolve_left hc
  apply e.injective
  change e a=e (e.symm 1)
  rw [h1, e.apply_symm_apply]

theorem eq_zero_or_topClass (n : ℕ) (hn : 1≤n) (a : cohomologyZMod2 (sphere n) n) :
    a=0 ∨ a=topClass n hn := by
  by_cases h : a=0
  · exact Or.inl h
  · exact Or.inr (eq_topClass_of_ne_zero n hn a h)

theorem existsUnique_nonzero (n : ℕ) (hn : 1≤n) : ∃! a : cohomologyZMod2 (sphere n) n, a≠0 :=
  ⟨topClass n hn,topClass_ne_zero n hn,fun a ha => eq_topClass_of_ne_zero n hn a ha⟩

open Finsler.IntervalSobolev Finsler.BorelLoop MeasureTheory

theorem constantValue_continuous (n : ℕ) : Continuous (constantValue : Finsler.SphereGeometry.Ambient n → ValueLp n) := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  change Continuous (Lp.constL 2 intervalMeasure ℝ : Finsler.SphereGeometry.Ambient n →L[ℝ] ValueLp n)
  exact ContinuousLinearMap.continuous _

theorem constantData_continuous (n : ℕ) : Continuous (constantData : Finsler.SphereGeometry.Ambient n → Space n) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_iff_value_velocity.mpr
  constructor
  · simpa only [value_constantData] using (constantValue_continuous n).continuousAt.tendsto
  · simpa only [velocity_constantData] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : Finsler.SphereGeometry.Ambient n => (0 : ValueLp n)) (𝓝 x) (𝓝 0))

theorem constantSphereLoop_continuous (n : ℕ) : Continuous (constantSphereLoop : Finsler.SphereGeometry.Sphere n → SphereLoop n) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply sphereLoop_tendsto_iff.mpr
  exact ((constantData_continuous n).comp continuous_subtype_val).continuousAt.tendsto

def fullSection (n : ℕ) : sphere n ⟶ (fullPair n).fst :=
  TopCat.ofHom ⟨fun x => ⟨constantSphereLoop x,Set.mem_univ _⟩,
    (constantSphereLoop_continuous n).subtype_mk _⟩

def levSection {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) : sphere n ⟶ (levPair F a).fst :=
  TopCat.ofHom ⟨fun x => ⟨constantSphereLoop x,Or.inr ⟨x,rfl⟩⟩,
    (constantSphereLoop_continuous n).subtype_mk _⟩

theorem fullSection_eval (n : ℕ) : fullSection n ≫ fullEval n=𝟙 (sphere n) := by
  ext x : 1
  exact eval_constant x

theorem levSection_eval {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) :
    levSection F a ≫ levEval F a=𝟙 (sphere n) := by
  ext x : 1
  exact eval_constant x

theorem fullSection_pull_e (n p : ℕ) (s : cohomologyZMod2 (sphere n) p) :
    (cohPullback (fullSection n) p).hom (eFull n p s)=s := by
  rw [eFull, ← Finsler.Cup.pullback_comp, fullSection_eval]
  have h := congrArg (fun φ => φ.hom s) ((singularCohomologyZMod2 p).map_id (Opposite.op (sphere n)))
  exact h

theorem levSection_pull_e {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) : (cohPullback (levSection F a) p).hom (eLev F a p s)=s := by
  rw [eLev, ← Finsler.Cup.pullback_comp, levSection_eval]
  have h := congrArg (fun φ => φ.hom s) ((singularCohomologyZMod2 p).map_id (Opposite.op (sphere n)))
  exact h

theorem eFull_injective (n p : ℕ) : Function.Injective (eFull n p) := by
  intro s t h
  have he := congrArg (fun a => (cohPullback (fullSection n) p).hom a) h
  simpa only [fullSection_pull_e] using he

theorem eLev_injective {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ) :
    Function.Injective (eLev F a p) := by
  intro s t h
  have he := congrArg (fun z => (cohPullback (levSection F a) p).hom z) h
  simpa only [levSection_pull_e] using he

/-- Canonical ordinary ambient evaluation class; its relative Borel action is defined separately. -/
def eFullTop (n : ℕ) (hn : 1≤n) := eFull n n (topClass n hn)
def eLevTop {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :=
  eLev F a n (topClass n hn)

theorem eFullTop_ne_zero (n : ℕ) (hn : 1≤n) : eFullTop n hn≠0 := by
  intro h
  apply topClass_ne_zero n hn
  apply eFull_injective n n
  simpa only [eFullTop,eFull,map_zero] using h

theorem eLevTop_ne_zero {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    eLevTop F a hn≠0 := by
  intro h
  apply topClass_ne_zero n hn
  apply eLev_injective F a n
  simpa only [eLevTop,eLev,map_zero] using h

/-- Positive-degree homology outside the actual sphere dimension vanishes. -/
theorem homology_isZero_of_ne (n k : ℕ) (hk : 1≤k) (hkn : k≠n) :
    CategoryTheory.Limits.IsZero (homologyZMod2 (sphere n) k) := by
  cases k with
  | zero => omega
  | succ j =>
    have hd : Module.finrank ℝ (Finsler.SphereGeometry.Ambient n)=n+1 :=
      (Finsler.SphereGeometry.ambientDimension n).out
    exact (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne
      (ModuleCat.of (ZMod 2) (ZMod 2)) hd hkn).of_iso
      ((TauCeti.reducedSingularHomologySuccIso (ModuleCat.of (ZMod 2) (ZMod 2)) j).app (sphere n)).symm

/-- The actual mod-two sphere cohomology is zero in every positive degree other than n. -/
theorem cohomology_eq_zero_of_ne (n k : ℕ) (hk : 1≤k) (hkn : k≠n)
    (a : cohomologyZMod2 (sphere n) k) : a=0 := by
  let : Subsingleton (homologyZMod2 (sphere n) k) :=
    ModuleCat.subsingleton_of_isZero (homology_isZero_of_ne n k hk hkn)
  apply (kroneckerEquiv (sphere n) k).toLinearEquiv.injective
  ext z
  have hz : z=0 := Subsingleton.elim _ _
  rw [hz, map_zero, map_zero]

theorem cohomology_subsingleton_of_ne (n k : ℕ) (hk : 1≤k) (hkn : k≠n) :
    Subsingleton (cohomologyZMod2 (sphere n) k) := by
  exact ⟨fun a b => (cohomology_eq_zero_of_ne n k hk hkn a).trans
    (cohomology_eq_zero_of_ne n k hk hkn b).symm⟩

/-- The canonical top class has square zero, by the sphere dimension calculation. -/
theorem topClass_cup_self (n : ℕ) (hn : 1≤n) :
    cupZMod2 (topClass n hn) (topClass n hn)=0 :=
  cohomology_eq_zero_of_ne n (n+n) (by omega) (by omega) _

end
end Finsler.SphereTopClass
