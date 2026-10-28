import LinearizedCompiler

namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT

set_option maxRecDepth 18000

def checkedEqual (i : Fin (StructuredCalls.size commonPrefix + 1)) : Bool :=
  decide ((fastArray[i.val]?).getD Instr.halt = program.code i)

/-- Executable differential against the unmodified upstream source's code
at every visited or sampled label. No claim of a full theorem without a
complete checked domain. -/
def checkFirst (count : Nat) : Nat × Nat := Id.run do
  let mut tested := 0
  let mut failed := 0
  for i in [:min count (StructuredCalls.size commonPrefix + 1)] do
    let j : Fin (StructuredCalls.size commonPrefix + 1) := Fin.ofNat _ i
    tested := tested + 1
    if !checkedEqual j then failed := failed + 1
  return (tested,failed)

end IndependentNonterminal

def main (args : List String) : IO Unit := do
  let count := (args.head?.bind String.toNat?).getD 60
  let (tested,failed) := IndependentNonterminal.checkFirst count
  IO.println s!"source_code_vs_flat_compared={tested};mismatches={failed}"
  if failed != 0 then throw <| IO.userError "Source code vs linearized compiler mismatch"
