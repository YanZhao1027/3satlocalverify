import MeasureHashABI
import FastLinearizedCompiler

/-! Validate the tail/difference-list linearizer against the original 16x44
ABI program: every static opcode label plus the full original execution state
for all 3585 steps. This prevents accepting a fast compiler just because it
produces the same final numeric answer. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 19000
set_option maxHeartbeats 1200000

def fastABIArray : Array (Instr 16 44 (StructuredCalls.size originalABI + 1)) :=
  IndependentNonterminal.FastLinearize.instructionArray originalABI

def originalABIProgram := StructuredCalls.compiled originalABI 0 39

def allABIInstructionsMatch : Bool := Id.run do
  let mut good := true
  for i in [:fastABIArray.size] do
    if h : i < StructuredCalls.size originalABI + 1 then
      good := good && ((fastABIArray[i]?).getD .halt == originalABIProgram.code ⟨i,h⟩)
    else good := false
  return good

def fastStep (table : Array (Instr 16 44 (StructuredCalls.size originalABI + 1)))
    (c : Cfg 16 44 (StructuredCalls.size originalABI + 1)) : Option (Cfg 16 44 (StructuredCalls.size originalABI + 1)) :=
  match c.pc with
  | none => none
  | some pc => (table[pc.val]?).map (fun op => BitProgram.execInstr op c)

end IndependentNativeCost

def main : IO Unit := do
  let a := IndependentNativeCost.allABIInstructionsMatch
  IO.println s!"FAST_LINEARIZER_ABI_STATIC_OPCODES_637_MATCH={a}"
  unless a do throw <| IO.userError "Tail linearizer opcode mismatch on original ABI"
  let p := IndependentNativeCost.originalABIProgram
  let start := IndependentNativeCost.actualABIInput.withPC (some p.entry)
  let orig := (List.range 3585).foldl (fun c _ => (OAI.Algorithms.SubexponentialSAT.BitProgram.step p c).getD c) start
  let fastTable := IndependentNativeCost.fastABIArray
  let fast := (List.range 3585).foldl (fun c _ =>
    (IndependentNativeCost.fastStep fastTable c).getD c) start
  let equal := orig.pc == fast.pc && orig.regs == fast.regs && orig.stacks == fast.stacks
  IO.println s!"FAST_LINEARIZER_ABI_FULL_STATE_3585_EQUAL={equal}"
  unless equal do throw <| IO.userError "Tail linearizer state diverged from original ABI"
