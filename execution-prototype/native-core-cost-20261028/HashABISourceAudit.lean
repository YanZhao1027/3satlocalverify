import MeasureHashABI

/-! All opcode locations and the ENTIRE original full-state bit-machine
execution of the true HashParametersProgram.ABI.command are compared to the
independent dense linearizer and compact interpreter, with no fake step
reports. This is a finite test, NOT a general theorem for all commands. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 19000
set_option maxHeartbeats 1200000

def trueOriginalABIProgram := StructuredCalls.compiled originalABI 0 39

def compareStaticABI : Nat × Nat := Id.run do
  let table : Array (Instr 16 44 (StructuredCalls.size originalABI + 1)) :=
    IndependentNonterminal.Linearize.instructionArray originalABI
  let mut checked := 0
  let mut fails := 0
  for i in [:table.size] do
    if h : i < StructuredCalls.size originalABI + 1 then
      checked := checked + 1
      unless (table[i]?).getD .halt == trueOriginalABIProgram.code ⟨i,h⟩ do
        fails := fails + 1
    else
      fails := fails + 1
  return (checked,fails)

def originalAfter (fuel : Nat) :=
  (List.range fuel).foldl
    (fun cfg _ => (BitProgram.step trueOriginalABIProgram cfg).getD cfg)
    (actualABIInput.withPC (some trueOriginalABIProgram.entry))

def exactStateEquality (fuel : Nat) : Bool := Id.run do
  let table : Array (Instr 16 44 (StructuredCalls.size originalABI + 1)) :=
    IndependentNonterminal.Linearize.instructionArray originalABI
  let old := copyConfig (originalAfter fuel)
  let (new,_stats) := runInstrumented table
    (copyConfig (actualABIInput.withPC (some trueOriginalABIProgram.entry))) fuel
  return old.pc == new.pc && old.registers == new.registers && old.words == new.words

end IndependentNativeCost

def main (args : List String) : IO Unit := do
  let steps := (args.head?.bind String.toNat?).getD 0
  let (checked,failures) := IndependentNativeCost.compareStaticABI
  IO.println s!"HASH_ABI_ORIGINAL_OPCODE checked={checked} mismatches={failures}"
  unless failures==0 && checked==637 do throw <| IO.userError "Mismatch in real ABI instructions"
  if steps > 0 then
    let equal := IndependentNativeCost.exactStateEquality steps
    IO.println s!"HASH_ABI_ORIGINAL_TRACE steps={steps} fullMachineStateEqual={equal}"
    unless equal do throw <| IO.userError "Mismatch in ABI original vs compact execution"
