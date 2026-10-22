module

public import Finsler.Topology.BorelCup
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-! Free involutions: w acts as zero. A contraction of the transfer 1 + t of an involutive
cochain complex is a family of linear maps Q commuting with the differential with
Q(1 + t) + (1 + t)Q = 1. Applying Q componentwise to a Borel cocycle c gives a Borel cochain of
the same support with total differential c, so every Borel class of degree n dies in degree
n + 1 under the inclusion w. For the relative singular cochains of a pair with an involution r,
a 0-cocycle π of the space with π + r^*π = 1 gives the contraction Q = (π ⌣ ·) ∘ r^*, by the
Leibniz rule, naturality and the unit law of the relative cup product. A function on the points
which is constant along singular 1-simplices defines such a 0-cocycle; this applies to the
indicator of a closed and open set U. Hence, if the involution exchanges U with its complement,
w acts as zero on the reflection Borel cohomology of the pair. -/

@[expose] public section

namespace Finsler.BorelFree

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair Convexity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A contraction of the transfer 1 + t compatible with the differential. -/
structure Contraction (K : InvComplex) where
  Q : (j : ℕ) → K.C j →ₗ[ZMod 2] K.C j
  comm_d : ∀ j x, K.d j (Q j x) = Q (j + 1) (K.d j x)
  homotopy : ∀ j x, Q j (tr K j x) + tr K j (Q j x) = x

section Algebra

variable {K : InvComplex} (h : Contraction K)

/-- The contraction applied componentwise. -/
def qSeq : Seq K →ₗ[ZMod 2] Seq K := LinearMap.pi fun j => h.Q j ∘ₗ LinearMap.proj j

theorem qSeq_apply (c : Seq K) (j : ℕ) : qSeq h c j = h.Q j (c j) := rfl

theorem qSeq_low {k : ℕ} {c : Seq K} (hc : c ∈ low K k) : qSeq h c ∈ low K k := by
  intro j hj
  rw [qSeq_apply, hc j hj, map_zero]

theorem tr_Q (j : ℕ) (x : K.C j) : tr K j (h.Q j x) = x + h.Q j (tr K j x) := by
  have e := h.homotopy j x
  calc tr K j (h.Q j x)
      = (h.Q j (tr K j x) + h.Q j (tr K j x)) + tr K j (h.Q j x) := by
        rw [two_eq_zero_of_mod, zero_add]
    _ = h.Q j (tr K j x) + (h.Q j (tr K j x) + tr K j (h.Q j x)) := by abel
    _ = x + h.Q j (tr K j x) := by rw [e, add_comm]

/-- The total differential of the contracted sequence. -/
theorem D_qSeq (c : Seq K) : D K (qSeq h c) = c + qSeq h (D K c) := by
  funext j
  cases j with
  | zero => rw [D_zero, qSeq_apply, tr_Q, Pi.add_apply, qSeq_apply, D_zero]
  | succ j =>
    rw [D_succ, qSeq_apply, qSeq_apply, h.comm_d, tr_Q, Pi.add_apply, qSeq_apply, D_succ,
      map_add]
    abel

include h in
/-- With a contraction of the transfer, w acts as zero on Borel cohomology. -/
theorem w_eq_zero (n : ℕ) (y : HR K n) : w K n y = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hc := (mem_bcocycles K).mp c.2
  change (Submodule.Quotient.mk (Submodule.inclusion (bcocycles_mono K n) c) : HR K (n + 1)) = 0
  rw [mk_eq_zero_iff_bcoboundary]
  refine ⟨qSeq h (c : Seq K), qSeq_low h hc.1, ?_⟩
  rw [D_qSeq, hc.2, map_zero, add_zero]
  rfl

end Algebra

section Cup

variable (P : TopPair.{0})

theorem cast_add {m n : ℕ} (h : m = n) (x y : RelativeCupCochain.relative P m) :
    RelativeCupCochain.cast P h (x + y) =
      RelativeCupCochain.cast P h x + RelativeCupCochain.cast P h y := by
  subst n
  rfl

theorem cast_smul {m n : ℕ} (h : m = n) (a : ZMod 2) (x : RelativeCupCochain.relative P m) :
    RelativeCupCochain.cast P h (a • x) = a • RelativeCupCochain.cast P h x := by
  subst n
  rfl

theorem cast_trans {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : RelativeCupCochain.relative P a) :
    RelativeCupCochain.cast P h₂ (RelativeCupCochain.cast P h₁ x) =
      RelativeCupCochain.cast P (h₁.trans h₂) x := by
  subst b
  subst c
  rfl

theorem differential_cast {m n : ℕ} (h : m = n) (x : RelativeCupCochain.relative P m) :
    RelativeCupCochain.differential P n (RelativeCupCochain.cast P h x) =
      RelativeCupCochain.cast P (congrArg (· + 1) h) (RelativeCupCochain.differential P m x) := by
  subst n
  rfl

theorem pullback_cast {P Q : TopPair.{0}} (f : P ⟶ Q) {m n : ℕ} (h : m = n)
    (x : RelativeCupCochain.relative Q m) :
    RelativeCupCochain.pullback f n (RelativeCupCochain.cast Q h x) =
      RelativeCupCochain.cast P h (RelativeCupCochain.pullback f m x) := by
  subst n
  rfl

/-- Multiplication of relative cochains by a 0-cochain of the space, in the same degree. -/
def mul (π : singularCochainGroup (ZMod 2) P.fst 0) (j : ℕ) :
    RelativeCupCochain.relative P j →ₗ[ZMod 2] RelativeCupCochain.relative P j where
  toFun ψ := RelativeCupCochain.cast P (Nat.zero_add j) (RelativeCupCochain.cup P 0 j π ψ)
  map_add' x y := by rw [RelativeCupCochain.add_right, cast_add]
  map_smul' a x := by
    rw [RelativeCupCochain.smul_right, cast_smul]
    rfl

theorem mul_apply (π : singularCochainGroup (ZMod 2) P.fst 0) (j : ℕ)
    (ψ : RelativeCupCochain.relative P j) :
    mul P π j ψ =
      RelativeCupCochain.cast P (Nat.zero_add j) (RelativeCupCochain.cup P 0 j π ψ) := rfl

theorem mul_add_left (π π' : singularCochainGroup (ZMod 2) P.fst 0) (j : ℕ)
    (ψ : RelativeCupCochain.relative P j) :
    mul P (π + π') j ψ = mul P π j ψ + mul P π' j ψ := by
  rw [mul_apply, mul_apply, mul_apply, RelativeCupCochain.add_left, cast_add]

theorem mul_one (j : ℕ) (ψ : RelativeCupCochain.relative P j) :
    mul P (cochainOne (R := ZMod 2) (Z := P.fst)) j ψ = ψ :=
  CupUnit.relative_cochain_one_left P j ψ

theorem differential_mul (π : singularCochainGroup (ZMod 2) P.fst 0)
    (hπ : cochainCoboundary (ZMod 2) P.fst 0 π = 0) (j : ℕ)
    (ψ : RelativeCupCochain.relative P j) :
    RelativeCupCochain.differential P j (mul P π j ψ) =
      mul P π (j + 1) (RelativeCupCochain.differential P j ψ) := by
  have hz : ∀ z : RelativeCupCochain.relative P (0 + j + 1),
      (0 : RelativeCupCochain.relative P (0 + j + 1)) + z = z := fun z => zero_add z
  rw [mul_apply, mul_apply, differential_cast, RelativeCupCochain.differential_cup, hπ,
    RelativeCupCochain.zero_left, RelativeCupCochain.cast_zero, hz, cast_trans]

theorem pullback_mul {P Q : TopPair.{0}} (f : P ⟶ Q)
    (π : singularCochainGroup (ZMod 2) Q.fst 0) (j : ℕ) (ψ : RelativeCupCochain.relative Q j) :
    RelativeCupCochain.pullback f j (mul Q π j ψ) =
      mul P (cochainPullback (TopPair.Hom.fst f) 0 π) j (RelativeCupCochain.pullback f j ψ) := by
  rw [mul_apply, mul_apply, pullback_cast, RelativeCupCochain.naturality]

variable (r : P ⟶ P) (π : singularCochainGroup (ZMod 2) P.fst 0)

theorem comm_d_aux (hδ : cochainCoboundary (ZMod 2) P.fst 0 π = 0) (j : ℕ)
    (x : RelativeCupCochain.relative P j)
    (htd : RelativeCupCochain.pullback r (j + 1) (RelativeCupCochain.differential P j x) =
      RelativeCupCochain.differential P j (RelativeCupCochain.pullback r j x)) :
    RelativeCupCochain.differential P j (mul P π j (RelativeCupCochain.pullback r j x)) =
      mul P π (j + 1)
        (RelativeCupCochain.pullback r (j + 1) (RelativeCupCochain.differential P j x)) := by
  rw [differential_mul P π hδ, htd]

theorem homotopy_aux
    (hπ : π + cochainPullback (TopPair.Hom.fst r) 0 π = cochainOne (R := ZMod 2) (Z := P.fst))
    (j : ℕ) (x : RelativeCupCochain.relative P j)
    (htt : RelativeCupCochain.pullback r j (RelativeCupCochain.pullback r j x) = x) :
    mul P π j (RelativeCupCochain.pullback r j (x + RelativeCupCochain.pullback r j x)) +
      (mul P π j (RelativeCupCochain.pullback r j x) +
        RelativeCupCochain.pullback r j (mul P π j (RelativeCupCochain.pullback r j x))) = x := by
  have h1 : mul P π j x + mul P (cochainPullback (TopPair.Hom.fst r) 0 π) j x = x := by
    rw [← mul_add_left, hπ, mul_one]
  rw [map_add, map_add, htt, pullback_mul, htt]
  calc mul P π j (RelativeCupCochain.pullback r j x) + mul P π j x +
        (mul P π j (RelativeCupCochain.pullback r j x) +
          mul P (cochainPullback (TopPair.Hom.fst r) 0 π) j x)
      = (mul P π j (RelativeCupCochain.pullback r j x) +
          mul P π j (RelativeCupCochain.pullback r j x)) +
        (mul P π j x + mul P (cochainPullback (TopPair.Hom.fst r) 0 π) j x) := by abel
    _ = x := by rw [two_eq_zero_of_mod, zero_add, h1]

/-- The contraction of the transfer of the relative cochains of a pair with involution r from
a 0-cocycle π with π + r^*π = 1. -/
def contraction (hr : r ≫ r = 𝟙 P) (hδ : cochainCoboundary (ZMod 2) P.fst 0 π = 0)
    (hπ : π + cochainPullback (TopPair.Hom.fst r) 0 π = cochainOne (R := ZMod 2) (Z := P.fst)) :
    Contraction (ofPair P r hr) where
  Q j := mul P π j ∘ₗ (ofPair P r hr).t j
  comm_d j x := comm_d_aux P r π hδ j x ((ofPair P r hr).td j x)
  homotopy j x := homotopy_aux P r π hπ j x ((ofPair P r hr).tt j x)

end Cup

section Point

variable (X : TopCat.{0})

/-- The point of a singular 0-simplex. -/
def simplexPoint (τ : singularSimplices X 0) : X :=
  X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 0)) τ default

/-- The 0-cochain of a function on the points of the space. -/
def pointCochain (g : X → ZMod 2) : singularCochainGroup (ZMod 2) X 0 :=
  Limits.Sigma.desc (fun τ : singularSimplices X 0 =>
    ModuleCat.ofHom (g (simplexPoint X τ) • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))

theorem pointCochain_eval (g : X → ZMod 2) (τ : singularSimplices X 0) :
    cochainEval 0 (pointCochain X g) τ = g (simplexPoint X τ) := by
  unfold cochainEval pointCochain
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (Limits.Sigma.ι_comp_desc (fun τ : singularSimplices X 0 =>
      ModuleCat.ofHom (g (simplexPoint X τ) • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))) τ))
    (1 : ZMod 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans (by simp)

/-- A function which is constant along singular 1-simplices defines a 0-cocycle. -/
theorem pointCochain_coboundary (g : X → ZMod 2)
    (hg : ∀ (σ : C(StdSimplex ℝ (Fin 2), X)) (x y : StdSimplex ℝ (Fin 2)), g (σ x) = g (σ y)) :
    cochainCoboundary (ZMod 2) X 0 (pointCochain X g) = 0 := by
  apply cochain_ext
  intro σ
  have key : ∀ i : Fin 2, g (simplexPoint X (AlexanderWhitney.faceSimplex X 0 i σ)) =
      g (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1)) σ default) := by
    intro i
    have e : simplexPoint X (AlexanderWhitney.faceSimplex X 0 i σ) =
        X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1)) σ
          (StdSimplex.map (SimplexCategory.δ i) default) := rfl
    rw [e]
    exact hg _ _ _
  rw [cochainCoboundary_eval, Fin.sum_univ_two, pointCochain_eval, pointCochain_eval, key 0,
    key 1, cochainEval_zero]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one, neg_mul]
  exact add_neg_cancel _

theorem pointCochain_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y → ZMod 2) :
    cochainPullback f 0 (pointCochain Y g) = pointCochain X (fun x => g (f.hom x)) := by
  apply cochain_ext
  intro τ
  rw [cochainPullback_eval, pointCochain_eval, pointCochain_eval]
  rfl

/-- The indicator of a closed and open set is constant along singular simplices. -/
theorem indicator_eq_of_isClopen {U : Set X} (hU : IsClopen U)
    (σ : C(StdSimplex ℝ (Fin 2), X)) (x y : StdSimplex ℝ (Fin 2)) :
    Set.indicator U (fun _ => (1 : ZMod 2)) (σ x) =
      Set.indicator U (fun _ => (1 : ZMod 2)) (σ y) := by
  have hpre : IsClopen (σ ⁻¹' U) := hU.preimage σ.continuous
  rcases isClopen_iff.mp hpre with h | h
  · have hx : σ x ∉ U := fun hx => by
      have hm : x ∈ σ ⁻¹' U := hx
      rw [h] at hm
      exact hm
    have hy : σ y ∉ U := fun hy => by
      have hm : y ∈ σ ⁻¹' U := hy
      rw [h] at hm
      exact hm
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · have hx : σ x ∈ U := by
      have hm : x ∈ σ ⁻¹' U := by
        rw [h]
        exact Set.mem_univ x
      exact hm
    have hy : σ y ∈ U := by
      have hm : y ∈ σ ⁻¹' U := by
        rw [h]
        exact Set.mem_univ y
      exact hm
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]

end Point

/-- If the involution of a pair exchanges a closed and open subset U of the space with its
complement, then w acts as zero on the reflection Borel cohomology of the pair. -/
theorem w_eq_zero_of_isClopen (P : TopPair.{0}) (r : P ⟶ P) (hr : r ≫ r = 𝟙 P)
    (U : Set P.fst) (hU : IsClopen U)
    (hswap : ∀ x : P.fst, (TopPair.Hom.fst r).hom x ∈ U ↔ x ∉ U) (n : ℕ)
    (y : HR (ofPair P r hr) n) : w (ofPair P r hr) n y = 0 := by
  have hδ : cochainCoboundary (ZMod 2) P.fst 0
      (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) = 0 :=
    pointCochain_coboundary P.fst _ (fun σ x y => indicator_eq_of_isClopen P.fst hU σ x y)
  have hπ : pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2))) +
      cochainPullback (TopPair.Hom.fst r) 0
        (pointCochain P.fst (Set.indicator U (fun _ => (1 : ZMod 2)))) =
      cochainOne (R := ZMod 2) (Z := P.fst) := by
    rw [pointCochain_pullback]
    apply cochain_ext
    intro τ
    rw [cochainEval_add, pointCochain_eval, pointCochain_eval, cochainOne_eval]
    by_cases hx : simplexPoint P.fst τ ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (fun h => ((hswap _).mp h) hx),
        add_zero]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem ((hswap _).mpr hx), zero_add]
  exact w_eq_zero (contraction P r _ hr hδ hπ) n y

end

end Finsler.BorelFree
