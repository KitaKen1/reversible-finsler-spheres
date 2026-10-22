module

public import Finsler.Algebra.ChainForm

/-! The index of an iterate of an iterate. The k-fold iterate of the d-fold iterate of a closed
chain of pair forms is the (d k)-fold iterate, after the identification of the residues modulo
k (d N) with the residues modulo (d k) N: the pair forms correspond, the chain forms correspond
under the induced linear isomorphism of the families, and the negative indices of inertia are
equal. Hence the index function of the d-fold iterated chain at k is the index function of the
chain at d k. -/

@[expose] public section

namespace Finsler.ChainIndexMul

open Module QuadraticMap Finsler.ChainForm

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (d k N : ℕ)

/-- The identification of the residues modulo k (d N) with the residues modulo (d k) N. -/
def reindex : ZMod (k * (d * N)) ≃+* ZMod (d * k * N) := ZMod.ringEquivCongr (by ring)

/-- The pair forms of the iterate of the iterate are the pair forms of the iterate. -/
theorem iter_iter (β : ZMod N → QuadraticForm ℝ (V × V)) (j : ZMod (k * (d * N))) :
    iter k (d * N) (iter d N β) j = iter (d * k) N β (reindex d k N j) := by
  have h := RingHom.ext_zmod
    ((ZMod.castHom (Dvd.intro_left d rfl) (ZMod N)).comp
      (ZMod.castHom (Dvd.intro_left k rfl) (ZMod (d * N))))
    ((ZMod.castHom (Dvd.intro_left (d * k) rfl) (ZMod N)).comp
      (reindex d k N : ZMod (k * (d * N)) →+* ZMod (d * k * N)))
  exact congrArg β (RingHom.congr_fun h j)

variable [NeZero d] [NeZero k] [NeZero N]

/-- The chain forms correspond under the identification of the indices. -/
theorem form_reindex (β : ZMod N → QuadraticForm ℝ (V × V)) (w : ZMod (d * k * N) → V) :
    form (iter k (d * N) (iter d N β)) (fun j => w (reindex d k N j)) =
      form (iter (d * k) N β) w := by
  rw [form_apply, form_apply]
  refine Fintype.sum_equiv (reindex d k N).toEquiv _ _ fun j => ?_
  change iter k (d * N) (iter d N β) j (w (reindex d k N j), w (reindex d k N (j + 1))) =
    iter (d * k) N β (reindex d k N j) (w (reindex d k N j), w (reindex d k N j + 1))
  rw [iter_iter, map_add, map_one]

/-- The negative indices of the two chain forms are equal. -/
theorem sigNeg_iter_iter (β : ZMod N → QuadraticForm ℝ (V × V)) :
    sigNeg (form (iter k (d * N) (iter d N β))) = sigNeg (form (iter (d * k) N β)) := by
  have hequiv : QuadraticMap.Equivalent (form (iter (d * k) N β))
      (form (iter k (d * N) (iter d N β))) :=
    ⟨⟨LinearEquiv.funCongrLeft ℝ V (reindex d k N).toEquiv, fun w => form_reindex d k N β w⟩⟩
  exact hequiv.sigNeg_eq.symm

/-- **The index of the k-fold iterate of the d-fold iterate is the index of the (d k)-fold
iterate.** -/
theorem idx_mul (β : ZMod N → QuadraticForm ℝ (V × V)) :
    idx (d * N) (iter d N β) k = idx N β (d * k) := by
  rw [idx_eq (d * N) (iter d N β) k, idx_eq N β (d * k)]
  exact sigNeg_iter_iter d k N β

end

end Finsler.ChainIndexMul
