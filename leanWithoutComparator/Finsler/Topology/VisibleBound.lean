module

public import Finsler.Topology.FixedGlobal

/-! A count for graded subspaces stable under v, and the bound of the visible K-classes. Let G
be a graded F₂-vector space with finite dimensional pieces, v a degree-one operator and fgt a
degree-zero map with fgt ∘ v = 0. For a family A of subspaces with v(A^q) ⊆ A^{q+1},

  Σ_{q ≤ D} dim fgt(A^q) ≤ dim A^D + Σ_{q < D} dim ker(v on G^q),

by rank–nullity for v and fgt on A^q in every degree. For the K-Borel cohomology of (t_{2a}, M)
at a regular cut, with A = E the restrictions of the global K-classes, the dimension of E^D in a
high degree D is at most the total rank of the restriction of global reflection classes to
(t_a, M). Hence the total dimension of the forgetful images of E is at most that total rank plus
the total dimension of the kernel of v. For a family T stable under v with T^D = 0 the count
bounds the total dimension of the forgetful images of T by the total dimension of the kernel of
v. -/

@[expose] public section

namespace Finsler.VisibleBound

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelLoop Finsler.BorelCochain
open Finsler.CriticalLevels Finsler.BorelIterate Finsler.BorelK Finsler.FiniteCut
open Finsler.FixedGlobal

noncomputable section

/-! ### The count -/

section Abstract

variable {G B : ℕ → Type} [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
  [∀ q, AddCommGroup (B q)] [∀ q, Module (ZMod 2) (B q)]
  [∀ q, Module.Finite (ZMod 2) (G q)]
  (v : ∀ q, G q →ₗ[ZMod 2] G (q + 1)) (fgt : ∀ q, G q →ₗ[ZMod 2] B q)
  (hfv : ∀ q x, fgt (q + 1) (v q x) = 0)
  (A : ∀ q, Submodule (ZMod 2) (G q)) (hA : ∀ q x, x ∈ A q → v q x ∈ A (q + 1))

include hfv hA in
/-- One step of the count. -/
theorem count_step (D : ℕ) :
    finrank (ZMod 2) (A D) + finrank (ZMod 2) ((A (D + 1)).map (fgt (D + 1))) ≤
      finrank (ZMod 2) (A (D + 1)) + finrank (ZMod 2) (LinearMap.ker (v D)) := by
  -- the forgetful map on A^{D+1}
  have h1 := LinearMap.finrank_range_add_finrank_ker ((fgt (D + 1)).domRestrict (A (D + 1)))
  rw [LinearMap.range_domRestrict] at h1
  -- v from A^D to A^{D+1}
  have h2 := LinearMap.finrank_range_add_finrank_ker ((v D).restrict (hA D))
  have h3 : LinearMap.range ((v D).restrict (hA D)) ≤
      LinearMap.ker ((fgt (D + 1)).domRestrict (A (D + 1))) := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (hfv D x)
  have h4 := Submodule.finrank_mono h3
  have h5 : (LinearMap.ker ((v D).restrict (hA D))).map (A D).subtype ≤ LinearMap.ker (v D) := by
    rintro _ ⟨x, hx, rfl⟩
    exact LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp hx))
  have h6 := Submodule.finrank_mono h5
  rw [Submodule.finrank_map_subtype_eq] at h6
  omega

include hfv hA in
/-- For a family of subspaces stable under v, the total dimension of the forgetful images up to
degree D is at most the dimension in degree D plus the total dimension of the kernel of v below
degree D. -/
theorem count (D : ℕ) :
    ∑ q ∈ Finset.range (D + 1), finrank (ZMod 2) ((A q).map (fgt q)) ≤
      finrank (ZMod 2) (A D) + ∑ q ∈ Finset.range D, finrank (ZMod 2) (LinearMap.ker (v q)) := by
  induction D with
  | zero =>
    rw [Finset.sum_range_one, Finset.sum_range_zero, add_zero]
    exact Submodule.finrank_map_le (fgt 0) (A 0)
  | succ D ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun q => finrank (ZMod 2) (LinearMap.ker (v q)))]
    have h := count_step v fgt hfv A hA D
    omega

end Abstract

/-! ### The visible K-classes at a regular cut -/

variable {n : ℕ} (F : ReversibleMetric n)

/-- With finitely many prime closed geodesic images, at a regular cut 2a and for D large: the
total dimension of the forgetful images of the restrictions to (t_{2a}, M) of the global
K-classes is at most the total rank of the restriction of global reflection classes to (t_a, M)
plus the total dimension of the kernel of v. -/
theorem exists_visible_bound (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q : ℕ, ∀ D, Q ≤ D →
      ∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
          ((LinearMap.range (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) ≤
        ∑ l ∈ Finset.range (D + 1), finrank (ZMod 2) (LinearMap.range (HRmap (resHom F a) l)) +
          ∑ q ∈ Finset.range D,
            finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) := by
  have h2 : 0 < 2 * a := by linarith
  obtain ⟨Q, hQ⟩ := exists_global_rank_le F hn hfin ha h2a
  have hfinK : ∀ q, Module.Finite (ZMod 2) (HK F (2 * a) q) := fun q =>
    finite_HK F hn hfin h2 h2a q
  refine ⟨Q, fun D hD => ?_⟩
  have hE : ∀ q x, x ∈ LinearMap.range (HRmap (borelHom (resComm F (2 * a))) q) →
      w (kComplex F (2 * a)) q x ∈
        LinearMap.range (HRmap (borelHom (resComm F (2 * a))) (q + 1)) := by
    intro q x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨w (kFull n) q y, HRmap_w (borelHom (resComm F (2 * a))) q y⟩
  have hfv : ∀ q (x : HK F (2 * a) q),
      forget (kComplex F (2 * a)) (q + 1) (w (kComplex F (2 * a)) q x) = 0 :=
    fun q x => (exact_forget (kComplex F (2 * a)) q _).mpr ⟨x, rfl⟩
  have hc := count (G := fun q => HK F (2 * a) q)
    (B := fun q => H (kComplex F (2 * a)) q)
    (fun q => w (kComplex F (2 * a)) q) (fun q => forget (kComplex F (2 * a)) q) hfv
    (fun q => LinearMap.range (HRmap (borelHom (resComm F (2 * a))) q)) hE D
  have hr := hQ D hD
  exact hc.trans (Nat.add_le_add_right hr _)

/-- With finitely many prime closed geodesic images, at a regular cut 2a: for a family T of
subspaces of the K-Borel cohomology of (t_{2a}, M) which is stable under v and vanishes in
degree D, the total dimension of the forgetful images of T is at most the total dimension of the
kernel of v below degree D. -/
theorem torsion_bound (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) (D : ℕ) (T : ∀ q, Submodule (ZMod 2) (HK F (2 * a) q))
    (hT : ∀ q x, x ∈ T q → w (kComplex F (2 * a)) q x ∈ T (q + 1)) (hTD : T D = ⊥) :
    ∑ q ∈ Finset.range (D + 1), finrank (ZMod 2) ((T q).map (forget (kComplex F (2 * a)) q)) ≤
      ∑ q ∈ Finset.range D, finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) := by
  have h2 : 0 < 2 * a := by linarith
  have hfinK : ∀ q, Module.Finite (ZMod 2) (HK F (2 * a) q) := fun q =>
    finite_HK F hn hfin h2 h2a q
  have hfv : ∀ q (x : HK F (2 * a) q),
      forget (kComplex F (2 * a)) (q + 1) (w (kComplex F (2 * a)) q x) = 0 :=
    fun q x => (exact_forget (kComplex F (2 * a)) q _).mpr ⟨x, rfl⟩
  have hc := count (G := fun q => HK F (2 * a) q) (B := fun q => H (kComplex F (2 * a)) q)
    (fun q => w (kComplex F (2 * a)) q) (fun q => forget (kComplex F (2 * a)) q) hfv T hT D
  have h0 : finrank (ZMod 2) (T D) = 0 := by
    rw [hTD]
    exact finrank_bot (ZMod 2) (HK F (2 * a) D)
  rw [h0, zero_add] at hc
  exact hc

end

end Finsler.VisibleBound
