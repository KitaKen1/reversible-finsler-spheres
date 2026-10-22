module

public import Finsler.Topology.BorelPair
public import Finsler.Topology.FilteredGysin
public import Finsler.Analysis.IntervalH1ReflectionAction

/-! The reflection Borel cohomology of the Finsler sublevel pairs. For a level a the pair is
(t_a, M), where M is the set of constant loops and t_a = {√E < a} ∪ M (so t_a = {√E < a} for
a > 0 and the pair is (M, M) for a ≤ 0); the reversal of loops preserves energy and fixes
constant loops, so it is an involution of every pair, compatible with the inclusions of the
pairs and of each pair into (Λ, M). The relative Borel cohomology B^q_a = H^q_R(t_a, M), the
ordinary cohomology A^q_a = H^q(t_a, M), the Gysin maps w, forget and transfer, the restrictions
from (Λ, M) and the cut maps for a ≤ b realize all exactness and naturality fields of the
filtered Gysin interface used by the detection argument. -/

@[expose] public section

namespace Finsler.BorelLoop

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevReverse Finsler.SobolevReflectionAction

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The loop space as a topological space. -/
abbrev Loops (n : ℕ) : TopCat.{0} := TopCat.of (SphereLoop n)

/-- The constant loops. -/
def consts (n : ℕ) : Set (Loops n) := range (constantSphereLoop : Sphere n → SphereLoop n)

/-- The sublevel together with the constant loops. -/
def lev (a : ℝ) : Set (Loops n) := energyCut F a ∪ consts n

theorem consts_subset_lev (a : ℝ) : consts n ⊆ lev F a := subset_union_right

theorem lev_mono {a b : ℝ} (hab : a ≤ b) : lev F a ⊆ lev F b :=
  union_subset_union_left _ (energyCut_mono F hab)

theorem reverse_mem_consts {u : SphereLoop n} (hu : u ∈ consts n) : reverseSphere u ∈ consts n := by
  obtain ⟨x, rfl⟩ := hu
  exact ⟨x, (reverseSphere_constant x).symm⟩

theorem reverse_mem_lev {a : ℝ} {u : SphereLoop n} (hu : u ∈ lev F a) :
    reverseSphere u ∈ lev F a := by
  rcases hu with hu | hu
  · left
    change Real.sqrt (energy F (reverseSphere u)) < a
    rw [energy_reverseSphere]
    exact hu
  · exact Or.inr (reverse_mem_consts hu)

/-- The pair (t, s) of nested subsets s ⊆ t. -/
abbrev pairOf {X : TopCat.{0}} {s t : Set X} (h : s ⊆ t) : TopPair.{0} :=
  TopPair.of (A := TopCat.of s) (X := TopCat.of t)
    (TopCat.ofHom (ContinuousMap.inclusion h)) (Topology.IsEmbedding.inclusion h)

/-- A continuous map t → t' carrying s into s' as a map of pairs. -/
def pairMap {X : TopCat.{0}} {s t s' t' : Set X} (hst : s ⊆ t) (hst' : s' ⊆ t')
    (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : X) ∈ s') : pairOf hst ⟶ pairOf hst' :=
  TopPair.ofHom (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x ↦ ⟨g ⟨x, hst x.2⟩, hg _ x.2⟩, by fun_prop⟩)

theorem pairMap_id {X : TopCat.{0}} {s t : Set X} (hst : s ⊆ t) :
    pairMap hst hst (ContinuousMap.id t) (fun _ hx ↦ hx) = 𝟙 (pairOf hst) := by
  ext : 2 <;> rfl

theorem pairMap_comp {X : TopCat.{0}} {s t s' t' s'' t'' : Set X} (hst : s ⊆ t)
    (hst' : s' ⊆ t') (hst'' : s'' ⊆ t'') (g : C(t, t')) (g' : C(t', t''))
    (hg : ∀ x : t, (x : X) ∈ s → (g x : X) ∈ s')
    (hg' : ∀ x : t', (x : X) ∈ s' → (g' x : X) ∈ s'') :
    pairMap hst hst'' (g'.comp g) (fun x hx ↦ hg' (g x) (hg x hx)) =
      pairMap hst hst' g hg ≫ pairMap hst' hst'' g' hg' := by
  ext : 2 <;> rfl

theorem pairMap_congr {X : TopCat.{0}} {s t s' t' : Set X} (hst : s ⊆ t) (hst' : s' ⊆ t')
    {g g' : C(t, t')} (h : g = g') (hg : ∀ x : t, (x : X) ∈ s → (g x : X) ∈ s')
    (hg' : ∀ x : t, (x : X) ∈ s → (g' x : X) ∈ s') :
    pairMap hst hst' g hg = pairMap hst hst' g' hg' := by
  subst h
  rfl

/-- The pair (t_a, M). -/
abbrev levPair (a : ℝ) : TopPair.{0} := pairOf (consts_subset_lev F a)

/-- The pair (Λ, M). -/
abbrev fullPair (n : ℕ) : TopPair.{0} := pairOf (subset_univ (consts n))

/-- The reversal on t_a. -/
def revLev (a : ℝ) : C(lev F a, lev F a) :=
  ⟨fun u => ⟨reverseSphere (u : SphereLoop n), reverse_mem_lev F u.2⟩,
    ((reverseSphere_continuous n).comp continuous_subtype_val).subtype_mk _⟩

/-- The reversal on Λ. -/
def revFull (n : ℕ) : C((univ : Set (Loops n)), (univ : Set (Loops n))) :=
  ⟨fun u => ⟨reverseSphere (u : SphereLoop n), mem_univ _⟩,
    ((reverseSphere_continuous n).comp continuous_subtype_val).subtype_mk _⟩

/-- The reversal as a map of pairs. -/
def revPair (a : ℝ) : levPair F a ⟶ levPair F a :=
  pairMap _ _ (revLev F a) (fun _ hx => reverse_mem_consts hx)

/-- The reversal of (Λ, M). -/
def revFullPair (n : ℕ) : fullPair n ⟶ fullPair n :=
  pairMap _ _ (revFull n) (fun _ hx => reverse_mem_consts hx)

theorem revPair_sq (a : ℝ) : revPair F a ≫ revPair F a = 𝟙 (levPair F a) := by
  have h : (revLev F a).comp (revLev F a) = ContinuousMap.id (lev F a) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverseSphere_involutive (u : SphereLoop n)) :
      (⟨reverseSphere (reverseSphere (u : SphereLoop n)), _⟩ : lev F a) = u)
  exact (pairMap_comp (consts_subset_lev F a) (consts_subset_lev F a) (consts_subset_lev F a)
    (revLev F a) (revLev F a) (fun _ hx => reverse_mem_consts hx)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem revFullPair_sq (n : ℕ) : revFullPair n ≫ revFullPair n = 𝟙 (fullPair n) := by
  have h : (revFull n).comp (revFull n) = ContinuousMap.id (univ : Set (Loops n)) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverseSphere_involutive (u : SphereLoop n)) :
      (⟨reverseSphere (reverseSphere (u : SphereLoop n)), mem_univ _⟩ : (univ : Set (Loops n))) = u)
  exact (pairMap_comp (subset_univ (consts n)) (subset_univ (consts n)) (subset_univ (consts n))
    (revFull n) (revFull n) (fun _ hx => reverse_mem_consts hx)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

/-- The inclusion t_a ⊆ t_b. -/
def inclLev {a b : ℝ} (hab : a ≤ b) : C(lev F a, lev F b) :=
  ⟨Set.inclusion (lev_mono F hab), continuous_inclusion _⟩

/-- The inclusion t_a ⊆ Λ. -/
def inclFull (a : ℝ) : C(lev F a, (univ : Set (Loops n))) :=
  ⟨Set.inclusion (subset_univ _), continuous_inclusion _⟩

/-- The inclusion of pairs (t_a, M) → (t_b, M). -/
def cutPair {a b : ℝ} (hab : a ≤ b) : levPair F a ⟶ levPair F b :=
  pairMap _ _ (inclLev F hab) (fun _ hx => hx)

/-- The inclusion of pairs (t_a, M) → (Λ, M). -/
def resPair (a : ℝ) : levPair F a ⟶ fullPair n :=
  pairMap _ _ (inclFull F a) (fun _ hx => hx)

theorem cutPair_equivariant {a b : ℝ} (hab : a ≤ b) :
    cutPair F hab ≫ revPair F b = revPair F a ≫ cutPair F hab := by
  have h : (revLev F b).comp (inclLev F hab) = (inclLev F hab).comp (revLev F a) := by
    ext u
    rfl
  exact (pairMap_comp _ _ _ (inclLev F hab) (revLev F b) (fun _ hx => hx)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => reverse_mem_consts hx)).trans
      (pairMap_comp _ _ _ (revLev F a) (inclLev F hab) (fun _ hx => reverse_mem_consts hx)
        (fun _ hx => hx)))

theorem resPair_equivariant (a : ℝ) :
    resPair F a ≫ revFullPair n = revPair F a ≫ resPair F a := by
  have h : (revFull n).comp (inclFull F a) = (inclFull F a).comp (revLev F a) := by
    ext u
    rfl
  exact (pairMap_comp _ _ _ (inclFull F a) (revFull n) (fun _ hx => hx)
    (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => reverse_mem_consts hx)).trans
      (pairMap_comp _ _ _ (revLev F a) (inclFull F a) (fun _ hx => reverse_mem_consts hx)
        (fun _ hx => hx)))

theorem cutPair_resPair {a b : ℝ} (hab : a ≤ b) :
    cutPair F hab ≫ resPair F b = resPair F a := by
  have h : (inclFull F b).comp (inclLev F hab) = inclFull F a := by
    ext u
    rfl
  exact (pairMap_comp _ _ _ (inclLev F hab) (inclFull F b) (fun _ hx => hx)
    (fun _ hx => hx)).symm.trans (pairMap_congr _ _ h _ (fun _ hx => hx))

/-- The involutive cochains of (t_a, M). -/
abbrev levComplex (a : ℝ) : InvComplex := ofPair (levPair F a) (revPair F a) (revPair_sq F a)

/-- The involutive cochains of (Λ, M). -/
abbrev fullComplex (n : ℕ) : InvComplex := ofPair (fullPair n) (revFullPair n) (revFullPair_sq n)

/-- Restriction from (Λ, M) to (t_a, M) on cochains. -/
abbrev resHom (a : ℝ) : InvHom (fullComplex n) (levComplex F a) :=
  pullHom (revPair_sq F a) (revFullPair_sq n) (resPair F a) (resPair_equivariant F a)

/-- Restriction from (t_b, M) to (t_a, M) on cochains. -/
abbrev cutHom {a b : ℝ} (hab : a ≤ b) : InvHom (levComplex F b) (levComplex F a) :=
  pullHom (revPair_sq F a) (revPair_sq F b) (cutPair F hab) (cutPair_equivariant F hab)

theorem Hmap_congr {K L : InvComplex} {φ ψ : InvHom K L} (h : ∀ j x, φ.f j x = ψ.f j x)
    (q : ℕ) (z : H K q) : Hmap φ q z = Hmap ψ q z := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk (cocycleMap φ q x) = Submodule.Quotient.mk (cocycleMap ψ q x)
  congr 1
  exact Subtype.ext (h q x)

theorem HRmap_congr {K L : InvComplex} {φ ψ : InvHom K L} (h : ∀ j x, φ.f j x = ψ.f j x)
    (q : ℕ) (z : HR K q) : HRmap φ q z = HRmap ψ q z := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk (bcocycleMap φ q c) = Submodule.Quotient.mk (bcocycleMap ψ q c)
  congr 1
  apply Subtype.ext
  funext j
  exact h j _

theorem cut_res_f {a b : ℝ} (hab : a ≤ b) (j : ℕ) (x : (fullComplex n).C j) :
    (invHomComp (resHom F b) (cutHom F hab)).f j x = (resHom F a).f j x := by
  have h := pullHom_comp (revPair_sq F a) (revPair_sq F b) (revFullPair_sq n) (cutPair F hab)
    (resPair F b) (cutPair_equivariant F hab) (resPair_equivariant F b)
    (by rw [cutPair_resPair]; exact resPair_equivariant F a) j x
  rw [← h]
  change ((pull (cutPair F hab ≫ resPair F b)).f j).hom x = ((pull (resPair F a)).f j).hom x
  rw [cutPair_resPair]

/-- The filtered Gysin system of the reflection Borel cohomology of the Finsler sublevels. -/
def gysinData :
    Finsler.FilteredGysin.Data (fun q => H (fullComplex n) q) (fun q => HR (fullComplex n) q)
      (fun a q => H (levComplex F a) q) (fun a q => HR (levComplex F a) q) where
  w q := (w (fullComplex n) q).toAddMonoidHom
  forget q := (forget (fullComplex n) q).toAddMonoidHom
  transfer q := (transfer (fullComplex n) q).toAddMonoidHom
  wB a q := (w (levComplex F a) q).toAddMonoidHom
  forgetB a q := (forget (levComplex F a) q).toAddMonoidHom
  transferB a q := (transfer (levComplex F a) q).toAddMonoidHom
  resA a q := (Hmap (resHom F a) q).toAddMonoidHom
  resB a q := (HRmap (resHom F a) q).toAddMonoidHom
  cutA a b hab q := (Hmap (cutHom F hab) q).toAddMonoidHom
  cutB a b hab q := (HRmap (cutHom F hab) q).toAddMonoidHom
  exact_forget q x := exact_forget (fullComplex n) q x
  exact_w q y := exact_w (fullComplex n) q y
  exact_wB a q y := exact_w (levComplex F a) q y
  natural_forget a q x := Hmap_forget (resHom F a) q x
  natural_w a q y := (HRmap_w (resHom F a) q y).symm
  natural_transfer a q z := HRmap_transfer (resHom F a) q z
  natural_cutA a b hab q z := by
    change Hmap (cutHom F hab) q (Hmap (resHom F b) q z) = Hmap (resHom F a) q z
    rw [← Hmap_comp]
    exact Hmap_congr (cut_res_f F hab) q z
  natural_cutB a b hab q y := by
    change HRmap (cutHom F hab) q (HRmap (resHom F b) q y) = HRmap (resHom F a) q y
    rw [← HRmap_comp]
    exact HRmap_congr (cut_res_f F hab) q y
  natural_cut_transfer a b hab q z := HRmap_transfer (cutHom F hab) q z

/-- The reflection Borel cohomology of the Finsler sublevel pairs realizes the exactness and
naturality fields of the filtered Gysin interface. -/
theorem exists_gysinData :
    Nonempty (Finsler.FilteredGysin.Data (fun q => H (fullComplex n) q)
      (fun q => HR (fullComplex n) q) (fun a q => H (levComplex F a) q)
      (fun a q => HR (levComplex F a) q)) :=
  ⟨gysinData F⟩

end

end Finsler.BorelLoop
