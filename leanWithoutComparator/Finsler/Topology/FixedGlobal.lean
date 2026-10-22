module

public import Finsler.Topology.LocalizeK

/-! Global K-classes on the fixed loops. The components of an iterated Borel class for a trivial
second involution are natural. Restriction of K-Borel cochains from (Λ, M) to the fixed pair of
the sublevel t_{2a} factors through the pair of all loops fixed by the half rotation, on which
the half rotation acts trivially; doubling maps (Λ, M) to this pair, compatibly with the doubling
of (t_a, M). Hence every component of the restriction of a global K-class to the fixed pair at
2a corresponds, under doubling, to the restriction to t_a of a global reflection class. With the
high-degree bijectivity of the restriction to the fixed pair this bounds the rank of the
restriction of global K-classes to (t_{2a}, M) in a high degree D by the total rank, in degrees at
most D, of the restriction of global reflection classes to (t_a, M). -/

@[expose] public section

namespace Finsler.FixedGlobal

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.SobolevHalfRoot Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.BorelIterate Finsler.BorelK Finsler.BorelFixed
open Finsler.CriticalLevels Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK
open Finsler.BorelCoverK Finsler.FiniteCut Finsler.LocalCoverK Finsler.EquivariantK
open Finsler.TrivialK Finsler.LocalizeK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Naturality of the components -/

/-- The components of an iterated Borel class for trivial second involutions are natural. -/
theorem theta_natural {K L : InvComplex} {SK : Commuting K} {SL : Commuting L}
    (hK : ∀ j x, SK.s j x = x) (hL : ∀ j x, SL.s j x = x) (Φ : CommHom SK SL) (m j : ℕ)
    (x : HR (borelInv SK) m) :
    theta SL hL m j (HRmap (borelHom Φ) m x) = HRmap Φ.φ j (theta SK hK m j x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- A bound for the rank of a map by the ranks of its components: if E is injective and every
component of E(R x) lies in a finite dimensional subspace p_i, the rank of R is at most the sum
of the dimensions of the p_i. -/
theorem finrank_range_le_of_components {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] {m : ℕ} {Y : Fin m → Type}
    [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod 2) (Y i)] (R : V →ₗ[ZMod 2] W)
    (E : W →ₗ[ZMod 2] ((i : Fin m) → Y i)) (hE : Function.Injective E)
    (p : ∀ i, Submodule (ZMod 2) (Y i)) [∀ i, Module.Finite (ZMod 2) (p i)]
    (h : ∀ x i, E (R x) i ∈ p i) :
    finrank (ZMod 2) (LinearMap.range R) ≤ ∑ i, finrank (ZMod 2) (p i) := by
  have hmem : ∀ (y : LinearMap.range R) (i : Fin m), E (y : W) i ∈ p i := by
    rintro ⟨_, x, rfl⟩ i
    exact h x i
  let f : LinearMap.range R →ₗ[ZMod 2] ((i : Fin m) → p i) :=
    LinearMap.pi fun i =>
      ((LinearMap.proj i ∘ₗ E ∘ₗ (LinearMap.range R).subtype).codRestrict (p i)
        (fun y => hmem y i))
  have hf : Function.Injective f := by
    intro y y' hyy
    apply Subtype.ext
    apply hE
    funext i
    exact congrArg (fun z : (i : Fin m) → p i => ((z i : p i) : Y i)) hyy
  have hfree : ∀ i, Module.Free (ZMod 2) (p i) := fun i => Module.Free.of_divisionRing _ _
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_pi_fintype] at h1
  exact h1

/-! ### The pair of all fixed loops -/

theorem kInv_univ : KInv (univ : Set (Loops n)) :=
  ⟨fun _ _ => mem_univ _, fun _ _ => mem_univ _⟩

theorem consts_subset_halfFixed : consts n ⊆ (halfFixedSet n : Set (Loops n)) := by
  rintro u ⟨x, rfl⟩
  exact const_mem_halfFixed x

theorem kInv_halfFixed : KInv (halfFixedSet n : Set (Loops n)) :=
  ⟨fun _ hu => reverse_mem_halfFixed hu, fun u hu => by
    have h : half +ᵥ u = u := hu
    rw [h]
    exact hu⟩

/-- The half rotation acts as the identity on the cochains of a pair of invariant sets of loops
fixed by it. -/
theorem kCommuting_trivial {s t : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    (hfix : ∀ u : SphereLoop n, u ∈ t → half +ᵥ u = u) :
    ∀ j x, (kCommuting hst hs ht).s j x = x := by
  intro j x
  have h : halfSet ht.half_mem = ContinuousMap.id t := by
    ext u
    exact hfix _ u.2
  have e : halfSub hst hs.half_mem ht.half_mem = 𝟙 (pairOf hst) :=
    (pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _)
  change ((pull (halfSub hst hs.half_mem ht.half_mem)).f j).hom x = x
  rw [e]
  exact pull_id_apply _ j x

/-- The reflection cochains of the pair of all loops fixed by the half rotation and the constant
loops. -/
abbrev fixAllComplex (n : ℕ) : InvComplex :=
  ofPair (pairOf (consts_subset_halfFixed (n := n)))
    (revSub consts_subset_halfFixed (kInv_consts (n := n)).rev_mem kInv_halfFixed.rev_mem)
    (revSub_sq consts_subset_halfFixed (kInv_consts (n := n)).rev_mem kInv_halfFixed.rev_mem)

/-- The two commuting involutions on them. -/
def fixAllCommuting (n : ℕ) : Commuting (fixAllComplex n) :=
  kCommuting (consts_subset_halfFixed (n := n)) kInv_consts kInv_halfFixed

theorem fixAllCommuting_trivial : ∀ j x, (fixAllCommuting n).s j x = x :=
  kCommuting_trivial consts_subset_halfFixed kInv_consts kInv_halfFixed fun _ hu => hu

/-! ### Restrictions -/

variable (F : ReversibleMetric n)

/-- Restriction from (Λ, M) to the pair of all fixed loops. -/
def resFixAll (n : ℕ) : CommHom (halfCommutingFull n) (fixAllCommuting n) :=
  kHom consts_subset_halfFixed kInv_consts kInv_halfFixed (subset_univ (consts n)) kInv_consts
    kInv_univ subset_rfl (subset_univ _)

/-- Restriction from the pair of all fixed loops to the fixed pair of the sublevel t_b. -/
def resFixCut (b : ℝ) : CommHom (fixAllCommuting n) (fixCommuting F b) :=
  kHom (consts_subset_fixLev F b) kInv_consts (kInv_fixLev F b) consts_subset_halfFixed
    kInv_consts kInv_halfFixed subset_rfl (fixLev_subset_halfFixed F b)

/-- Restriction from (t_b, M) to its fixed pair. -/
def resCutFix (b : ℝ) : CommHom (halfCommuting F b) (fixCommuting F b) :=
  kHom (consts_subset_fixLev F b) kInv_consts (kInv_fixLev F b) (consts_subset_lev F b)
    kInv_consts (kInv_lev F b) subset_rfl (fixLev_subset_lev F b)

/-- The two restrictions from (Λ, M) to the fixed pair of t_b agree on cochains. -/
theorem res_square (b : ℝ) (j : ℕ) (x : (fullComplex n).C j) :
    (resCutFix F b).φ.f j ((resComm F b).φ.f j x) =
      (resFixCut F b).φ.f j ((resFixAll n).φ.f j x) := by
  have h1 := pull_comp_apply (inclPair (consts_subset_fixLev F b) (consts_subset_lev F b)
    subset_rfl (fixLev_subset_lev F b)) (resPair F b) j x
  have h2 := pull_comp_apply (inclPair (consts_subset_fixLev F b)
    (consts_subset_halfFixed (n := n)) subset_rfl (fixLev_subset_halfFixed F b))
    (inclPair (consts_subset_halfFixed (n := n)) (subset_univ (consts n)) subset_rfl
      (subset_univ _)) j x
  have e : inclPair (consts_subset_fixLev F b) (consts_subset_lev F b) subset_rfl
      (fixLev_subset_lev F b) ≫ resPair F b =
      inclPair (consts_subset_fixLev F b) (consts_subset_halfFixed (n := n)) subset_rfl
        (fixLev_subset_halfFixed F b) ≫
        inclPair (consts_subset_halfFixed (n := n)) (subset_univ (consts n)) subset_rfl
          (subset_univ _) := by
    ext : 2 <;> rfl
  rw [e] at h1
  exact h1.symm.trans h2

/-! ### Doubling of all loops -/

/-- Doubling as a map from all loops to the fixed loops. -/
def dblAllMap (n : ℕ) : C((univ : Set (Loops n)), (halfFixedSet n : Set (Loops n))) :=
  ⟨fun u => ⟨(doubleSphere (u : SphereLoop n) : SphereLoop n),
      (doubleSphere (u : SphereLoop n)).2⟩,
    (continuous_subtype_val.comp
      ((doubleSphere_continuous n).comp continuous_subtype_val)).subtype_mk _⟩

theorem dblAll_mem_consts (u : (univ : Set (Loops n))) (hu : (u : Loops n) ∈ consts n) :
    ((dblAllMap n u : (halfFixedSet n : Set (Loops n))) : Loops n) ∈ consts n := by
  obtain ⟨x, hx⟩ := hu
  refine ⟨x, ?_⟩
  change constantSphereLoop x = (doubleSphere (u : SphereLoop n) : SphereLoop n)
  rw [← hx, doubleSphere_val, double_const]

/-- Doubling as a map of pairs from (Λ, M) to the pair of all fixed loops. -/
def dblAllPair (n : ℕ) : fullPair n ⟶ pairOf (consts_subset_halfFixed (n := n)) :=
  pairMap _ _ (dblAllMap n) dblAll_mem_consts

theorem dblAllPair_rev :
    dblAllPair n ≫ revSub consts_subset_halfFixed (kInv_consts (n := n)).rev_mem
      kInv_halfFixed.rev_mem = revFullPair n ≫ dblAllPair n := by
  have h : (revSet (kInv_halfFixed (n := n)).rev_mem).comp (dblAllMap n) =
      (dblAllMap n).comp (revFull n) := by
    ext u
    have e := reverse_double (u : SphereLoop n)
    exact e
  exact (pairMap_comp _ _ _ (dblAllMap n) (revSet (kInv_halfFixed (n := n)).rev_mem)
    dblAll_mem_consts (fun _ hx => reverse_mem_consts hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun u hx => dblAll_mem_consts _ (reverse_mem_consts hx))).trans
      (pairMap_comp _ _ _ (revFull n) (dblAllMap n) (fun _ hx => reverse_mem_consts hx)
        dblAll_mem_consts))

/-- Pullback of reflection cochains along the doubling of all loops. -/
def dblAllHom (n : ℕ) : InvHom (fixAllComplex n) (fullComplex n) :=
  pullHom (revFullPair_sq n)
    (revSub_sq consts_subset_halfFixed (kInv_consts (n := n)).rev_mem kInv_halfFixed.rev_mem)
    (dblAllPair n) dblAllPair_rev

/-- Doubling of (t_a, M) followed by the inclusion of the fixed pair is the inclusion of
(t_a, M) followed by the doubling of all loops. -/
theorem dbl_square_pair (a : ℝ) :
    dblPair F a ≫ inclPair (consts_subset_fixLev F (2 * a)) (consts_subset_halfFixed (n := n))
      subset_rfl (fixLev_subset_halfFixed F (2 * a)) = resPair F a ≫ dblAllPair n := by
  ext : 2 <;> rfl

/-- On reflection Borel cohomology: restriction to the fixed pair of t_{2a} followed by doubling
is doubling of all loops followed by restriction to t_a. -/
theorem dbl_square (a : ℝ) (l : ℕ) (y : HR (fixAllComplex n) l) :
    HRmap (dblHom F a) l (HRmap (resFixCut F (2 * a)).φ l y) =
      HRmap (resHom F a) l (HRmap (dblAllHom n) l y) := by
  rw [← HRmap_comp, ← HRmap_comp]
  refine HRmap_congr (fun j x => ?_) l y
  have h1 := pull_comp_apply (dblPair F a) (inclPair (consts_subset_fixLev F (2 * a))
    (consts_subset_halfFixed (n := n)) subset_rfl (fixLev_subset_halfFixed F (2 * a))) j x
  have h2 := pull_comp_apply (resPair F a) (dblAllPair n) j x
  rw [dbl_square_pair] at h1
  exact h1.symm.trans h2

/-! ### Components of global classes on the fixed pair -/

/-- Every component of the restriction of a global K-class to the fixed pair of t_{2a}
corresponds under doubling to the restriction to t_a of a global reflection class. -/
theorem theta_fixed_mem (a : ℝ) (D l : ℕ) (x : HR (kFull n) D) :
    (doublingEquiv F a l).symm (theta (fixCommuting F (2 * a)) (fixCommuting_trivial F (2 * a))
      D l (HRmap (borelHom (resCutFix F (2 * a))) D
        (HRmap (borelHom (resComm F (2 * a))) D x))) ∈
      LinearMap.range (HRmap (resHom F a) l) := by
  rw [HRmap_borelHom_comm (resComm F (2 * a)) (resCutFix F (2 * a)) (resFixAll n)
      (resFixCut F (2 * a)) (res_square F (2 * a)) D x,
    theta_natural fixAllCommuting_trivial (fixCommuting_trivial F (2 * a))
      (resFixCut F (2 * a))]
  change HRmap (dblHom F a) l (HRmap (resFixCut F (2 * a)).φ l
    (theta (fixAllCommuting n) fixAllCommuting_trivial D l
      (HRmap (borelHom (resFixAll n)) D x))) ∈ _
  rw [dbl_square]
  exact ⟨_, rfl⟩

/-- With finitely many prime closed geodesic images, at a regular cut 2a the rank of the
restriction of global K-classes of a high degree D to (t_{2a}, M) is at most the total rank, in
degrees at most D, of the restriction of global reflection classes to (t_a, M). -/
theorem exists_global_rank_le (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q : ℕ, ∀ D, Q ≤ D →
      finrank (ZMod 2) (LinearMap.range (HRmap (borelHom (resComm F (2 * a))) D)) ≤
        ∑ l ∈ Finset.range (D + 1),
          finrank (ZMod 2) (LinearMap.range (HRmap (resHom F a) l)) := by
  have hac : a ∉ crit F := fun h => h2a (crit_double F h)
  obtain ⟨Q, hbij⟩ := exists_bijective_fixed F hn hfin ha h2a
  obtain ⟨_, hfinR, -⟩ := exists_finite_HR F hn hfin ha hac
  refine ⟨Q, fun D hD => ?_⟩
  have hfinp : ∀ i : Fin (D + 1),
      Module.Finite (ZMod 2) (LinearMap.range (HRmap (resHom F a) i)) := fun i => by
    have := hfinR i
    exact Module.Finite.of_injective (LinearMap.range (HRmap (resHom F a) i)).subtype
      (Submodule.injective_subtype _)
  have hinj : Function.Injective (HRmap (borelHom (resCutFix F (2 * a))) D) := (hbij D hD).1
  have key := finrank_range_le_of_components (Y := fun i : Fin (D + 1) => HR (levComplex F a) i)
    (HRmap (borelHom (resComm F (2 * a))) D)
    (((trivSplit (fixCommuting F (2 * a)) (fixCommuting_trivial F (2 * a)) D).trans
        (LinearEquiv.piCongrRight fun i : Fin (D + 1) =>
          (doublingEquiv F a i).symm)).toLinearMap ∘ₗ
      HRmap (borelHom (resCutFix F (2 * a))) D)
    (fun y y' hyy => hinj
      (((trivSplit (fixCommuting F (2 * a)) (fixCommuting_trivial F (2 * a)) D).trans
        (LinearEquiv.piCongrRight fun i : Fin (D + 1) =>
          (doublingEquiv F a i).symm)).injective hyy))
    (fun i => LinearMap.range (HRmap (resHom F a) i))
    (fun x i => theta_fixed_mem F a D i x)
  rw [Fin.sum_univ_eq_sum_range
    (fun l => finrank (ZMod 2) (LinearMap.range (HRmap (resHom F a) l))) (D + 1)] at key
  exact key

end

end Finsler.FixedGlobal
