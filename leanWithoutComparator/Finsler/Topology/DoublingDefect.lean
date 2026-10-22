module

public import Finsler.Topology.LocalizeK

/-! The difference of the defects at the cuts a and 2a. At a regular cut the defect plus the
total rank of the restriction of global classes is the total dimension of the reflection Borel
cohomology of the cut. With the doubling rank formula
dim B_{2a} = dim B_a + 2 dim ker(v on the K-Borel cohomology of (t_{2a}, M)) this gives

  T(2a) − T(a) = 2 t − V(2a) + V(a),

where t is the total dimension of the kernel of v and V(c) is the total rank of the restriction
of global classes to the cut c. This is the numerical skeleton of the doubling inequality; the
decomposition of t and of the visible ranks into labels is not made here. -/

@[expose] public section

namespace Finsler.DoublingDefect

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelLoop Finsler.BorelCochain
open Finsler.CriticalLevels Finsler.BorelK Finsler.CutCount Finsler.LocalizeK

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The doubling difference of the defects: with finitely many prime closed geodesic images, at
a regular cut 2a, the defect at 2a minus the defect at a is twice the total dimension of the
kernel of v on the K-Borel cohomology of (t_{2a}, M), minus the total rank of the restriction of
global classes to t_{2a}, plus the total rank of their restriction to t_a. -/
theorem exists_defect_double (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q →
      (Defect.defect F (2 * a) : ℤ) - (Defect.defect F a : ℤ) =
        2 * ((∑ q ∈ Finset.range Q,
            finrank (ZMod 2) (LinearMap.ker (w (kComplex F (2 * a)) q)) : ℕ) : ℤ) -
          ((∑ q ∈ Finset.range Q,
            finrank (ZMod 2) (LinearMap.range (HRmap (resHom F (2 * a)) q)) : ℕ) : ℤ) +
          ((∑ q ∈ Finset.range Q,
            finrank (ZMod 2) (LinearMap.range (HRmap (resHom F a) q)) : ℕ) : ℤ) := by
  have hac : a ∉ crit F := fun h => h2a (crit_double F h)
  have h2 : 0 < 2 * a := by linarith
  obtain ⟨Q₁, h1⟩ := exists_defect_count F hn hfin ha hac
  obtain ⟨Q₂, h2'⟩ := exists_defect_count F hn hfin h2 h2a
  obtain ⟨Q₃, h3⟩ := exists_doubling_count F hn hfin ha h2a
  refine ⟨Q₁ + Q₂ + Q₃ + 1, fun Q hQ => ?_⟩
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  have e1 := h1 (Q' + 1) (by omega)
  have e2 := h2' (Q' + 1) (by omega)
  have e3 := h3 Q' (by omega)
  omega

end

end Finsler.DoublingDefect
