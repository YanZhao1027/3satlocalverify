import GeneralVEWeighted
import PrimePowerKernel

namespace GeneralVEDual11
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def lit (v : Fin 11) (p : Bool) : Literal (Fin 11) := ⟨v,p⟩
private def clause (ls : List (Literal (Fin 11))) : Clause (Fin 11) := ls.toFinset

/-- Eleven-variable, five-clause CONNECTED 3-CNF from previous experiments. -/
def F : CNF (Fin 11) :=
  ([clause [lit 0 true,lit 1 true,lit 2 true],
    clause [lit 2 false,lit 3 true,lit 4 true],
    clause [lit 4 false,lit 5 true,lit 6 true],
    clause [lit 6 false,lit 7 true,lit 8 true],
    clause [lit 8 false,lit 9 true,lit 10 true]] : List (Clause (Fin 11))).toFinset

/-- One call to the formally verified general bucket elimination computes BOTH
    the function value and derivative at the specified residue-ring node. -/
def jets (p : Nat) : Fin 3 → List (ZMod p) := fun i =>
  let d := GeneralVEWeighted.dualJet F (i.val : ZMod p)
  [d.fst,d.snd]

/-- Original OpenAI non-field, nilpotent Hermite/CRT implementation. -/
def r49 : List (ZMod 49) × Nat :=
  Reconstruction.run (PaperKernel.ops 49) (fun i : Fin 3 => (i.val : ZMod 49))
    7 2 2 (jets 49)

def r11 : List (ZMod 11) × Nat :=
  Reconstruction.run (PaperKernel.ops 11) (fun i : Fin 3 => (i.val : ZMod 11))
    11 1 2 (jets 11)

def r13 : List (ZMod 13) × Nat :=
  Reconstruction.run (PaperKernel.ops 13) (fun i : Fin 3 => (i.val : ZMod 13))
    13 1 2 (jets 13)

def exactByCRT : Nat :=
  PaperKernel.recover49_11_13 ((r49.1.headD 0).val)
    ((r11.1.headD 0).val) ((r13.1.headD 0).val)

#eval ((List.finRange 3).map fun i => (jets 49 i).map ZMod.val)
#eval (r49.1.take 6).map ZMod.val
#eval (r11.1.take 6).map ZMod.val
#eval (r13.1.take 6).map ZMod.val
#eval [r49.2,r11.2,r13.2]
#eval exactByCRT
#eval SAT.count F
#eval (exactByCRT == SAT.count F)

end GeneralVEDual11
