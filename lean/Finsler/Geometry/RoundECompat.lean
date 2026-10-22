module

public import Finsler.Geometry.RoundLoopCup
public import Finsler.Geometry.V2Euler
public import Finsler.Geometry.RoundStage13

/-! The e-compatibility of the round crossings, unconditionally, and stage 13 modulo G6b.

`V2Euler.eV_cupInj` (the cup with π^*[Sⁿ] is injective on H⁰(V₂)) and `RoundLoopCup.ecompat_of`
give `RoundFiltration.ECompat n hn` for every n ≥ 3. Hence the global basis of the round sphere
needs only the local K-lift `YTop` of the odd stages, and w^n = 0 on the reflection Borel
cohomology of (Λ, M) holds unconditionally. -/

@[expose] public section

namespace Finsler.RoundECompat

open Finsler.RoundFiltration Finsler.RoundKGlobal Finsler.RoundStage13 Finsler.BasisBudget
open Finsler.BorelLoop Finsler.NilpotentW Finsler.BorelCochain

noncomputable section

variable {n : ℕ}

/-- **The e-compatibility of the round crossings.** -/
theorem ecompat (hn : 3 ≤ n) : ECompat n hn :=
  Finsler.RoundLoopCup.ecompat_of hn (Finsler.V2Euler.eV_cupInj (by omega))

/-- **Stage 13 for the round sphere**, given only the local K-lift of the odd stages (G6b). -/
def stage13DataY (hn : 3 ≤ n) (hy : YTop n hn) : Data n (by omega) :=
  stage13Data hn (ecompat hn) hy

/-- **w^n = 0** on the reflection Borel cohomology of the loop space pair of the round sphere. -/
theorem round_w_nil_uncond (hn : 3 ≤ n) (lo : ℕ) (x : HR (fullComplex n) lo) :
    wPow (fullComplex n) lo n x = 0 :=
  stage13_w_nil hn (ecompat hn) lo x

end

end Finsler.RoundECompat
