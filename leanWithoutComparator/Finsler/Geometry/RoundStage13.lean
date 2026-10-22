module

public import Finsler.Geometry.RoundKGlobal
public import Finsler.Geometry.RoundSupports

/-! Stage 13 (BASIS) for the round sphere: the global basis and w-nilpotence.

With compact supports proved (`RoundSupports`), the global basis `BasisBudget.Data n` and
w^n = 0 on the reflection Borel cohomology of (Λ, M) follow for n ≥ 3 from exactly two local
inputs about the round crossings:

* `ECompat n hn`: the e-multiple of the start class of every round crossing is not forgotten to
  zero (e-compatibility of the local model);
* `YTop n hn`: at the odd stages the e-multiple of the start class lifts to K-Borel cohomology
  (G6b).

The w-nilpotence uses only `ECompat`. -/

@[expose] public section

namespace Finsler.RoundStage13

open Finsler.RoundFiltration Finsler.RoundTails Finsler.RoundKGlobal Finsler.RoundSupports
open Finsler.BorelCochain Finsler.BorelLoop Finsler.BasisBudget Finsler.NilpotentW

noncomputable section

variable {n : ℕ}

/-- **The global basis of the round sphere.** -/
def stage13Data (hn : 3 ≤ n) (he : ECompat n hn) (hy : YTop n hn) : Data n (by omega) :=
  roundData hn he (round_supports n) hy

/-- **w^n = 0** on the reflection Borel cohomology of the loop space pair. -/
theorem stage13_w_nil (hn : 3 ≤ n) (he : ECompat n hn) (lo : ℕ) (x : HR (fullComplex n) lo) :
    wPow (fullComplex n) lo n x = 0 :=
  round_w_nil hn he (round_supports n) lo x

end

end Finsler.RoundStage13
