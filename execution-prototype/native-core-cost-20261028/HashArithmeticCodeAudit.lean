import MeasureHashArithmetic

/-! Exhaustive dynamic opcode-by-opcode comparison for ALL 426 instruction
labels in the original 8-register, 22-stack arithmetic program. The source
is the pinned original program.code, never a precomputed expected answer.
An out-of-fuel check fails, as does any opcode or entry mismatch. -/

namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

def originalProgram := StructuredCalls.compiled realArithmeticCommand 0 14

def verifySourceOpcode (i : Nat) : Bool :=
  if h : i < StructuredCalls.size realArithmeticCommand + 1 then
    let flat : Array (Instr 8 22 (StructuredCalls.size realArithmeticCommand + 1)) :=
      IndependentNonterminal.Linearize.instructionArray realArithmeticCommand
    (flat[i]?).getD .halt == originalProgram.code ⟨i,h⟩
  else false

/-- Same original data and instruction count; compare full machine state. -/
def rawOriginalRun (fuel : Nat) :=
  (List.range fuel).foldl (fun c _ => (BitProgram.step originalProgram c).getD c)
    (arithmeticInput.withPC (some originalProgram.entry))

def originalVsCompact (fuel : Nat) : Bool := Id.run do
  let raw := copyConfig (rawOriginalRun fuel)
  let table : Array (Instr 8 22 (StructuredCalls.size realArithmeticCommand + 1)) :=
    IndependentNonterminal.Linearize.instructionArray realArithmeticCommand
  let input := copyConfig (arithmeticInput.withPC (some originalProgram.entry))
  let (fast,_) := runInstrumented table input fuel
  return raw.pc == fast.pc && raw.registers == fast.registers && raw.words == fast.words

end IndependentNativeCost

def main (args : List String) : IO Unit := do
  let count := (args[0]?.bind String.toNat?).getD 426
  let steps := (args[1]?.bind String.toNat?).getD 0
  let full := OAI.Algorithms.SubexponentialSAT.StructuredCalls.size
    IndependentNativeCost.realArithmeticCommand + 1
  unless 0 < count && count <= full do throw <| IO.userError "Invalid audit count"
  let mut different := 0
  for i in [:count] do
    unless IndependentNativeCost.verifySourceOpcode i do
      different := different + 1
  IO.println s!"ORIGINAL_HASH_OPCODE_AUDIT checked={count} tableSize={full} mismatches={different}"
  if different != 0 then throw <| IO.userError "Source opcode mismatch"
  if steps > 0 then
    let equal := IndependentNativeCost.originalVsCompact steps
    IO.println s!"ORIGINAL_HASH_STEP_AUDIT firstSteps={steps} fullStateEqual={equal}"
    unless equal do throw <| IO.userError "Source/array state mismatch"
