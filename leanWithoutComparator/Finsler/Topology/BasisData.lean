module

public import Finsler.Topology.GlobalK

/-! The global basis of `BasisBudget.Data` from abstract basis data on the loop space pair.

`BasisBudget.Data n hn` asks for exactly the fields of `GlobalK.AbsData` for the involutive
complex of (Λ, M), the commuting half rotation (`halfCommutingFull n`) and the evaluation cup
(`fullE n hn`). Hence a K-filtration of the loop space pair (`GlobalK.KGlobal`) with these
complexes gives the global basis and the nilpotence of w required by `CoreResidual.Inputs`. -/

@[expose] public section

namespace Finsler.BasisData

open Finsler.BorelCochain Finsler.BorelLoop Finsler.BorelK Finsler.BasisBudget
open Finsler.BorelCanonicalEvaluation Finsler.GlobalK

noncomputable section

/-- Abstract basis data on the loop space pair is a global basis. -/
def toData {n : ℕ} {hn : 1 ≤ n}
    (A : AbsData (fullComplex n) (halfCommutingFull n) n (fullE n hn)) : Data n hn where
  bot := A.bot
  top := A.top
  odd := A.odd
  torsion := A.torsion
  span := A.span
  top_eq := A.top_eq
  lift_bot := A.lift_bot
  lift_odd := A.lift_odd
  lift_top := A.lift_top
  odd_mem := A.odd_mem
  bot_ne := A.bot_ne

end

end Finsler.BasisData
