import LinearizedCompiler

/-! Exact *dynamic* opcode differential against upstream `program.code` for a
specified label interval. Split intervals to avoid one huge unbounded evaluator.
No trusted Lean theorem of global compiler equality is claimed. -/
namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 18000

def checkLabel (i : Nat) : Bool :=
  if h : i < StructuredCalls.size commonPrefix + 1 then
    let j : Fin (StructuredCalls.size commonPrefix + 1) := ⟨i,h⟩
    (fastArray[i]?).getD .halt == program.code j
  else false

end IndependentNonterminal

def main (args : List String) : IO Unit := do
  let start := (args[0]?.bind String.toNat?).getD 0
  let count := (args[1]?.bind String.toNat?).getD 1
  let total := OAI.Algorithms.SubexponentialSAT.StructuredCalls.size
    IndependentNonterminal.commonPrefix + 1
  unless count > 0 && start < total && start + count <= total do
    throw <| IO.userError "Invalid chunk range"
  let mut mismatches := 0
  for i in [start:start+count] do
    unless IndependentNonterminal.checkLabel i do
      mismatches := mismatches + 1
  IO.println s!"ORIGINAL_OPCODE_CHUNK start={start} count={count} checked={count} mismatches={mismatches} total={total}"
  if mismatches != 0 then throw <| IO.userError "One or more opcodes differ"
