import CompactNative40

/-! Verify the actual original upstream clause-count stage, rather than
relying on the new array compiler's self-report. Compare EVERY source opcode
and the entire 180-step original state to the independent array interpreter. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog

def clauseCmd := LeafProgram.ClauseCount.caller
def originalClauseProgram := StructuredCalls.compiled clauseCmd 784 788

def sourceRun180 :=
  (List.range 180).foldl
    (fun c _ => (BitProgram.step originalClauseProgram c).getD c)
    (loadedLocalInput.withPC (some originalClauseProgram.entry))

def smallAudit : Bool := Id.run do
  let code := IndependentNonterminal.Linearize.instructionArray clauseCmd
  let entryNum := IndependentNonterminal.Linearize.callEntry clauseCmd 1 0
  let mut codeOk := code.size == StructuredCalls.size clauseCmd + 1
  for i in [:code.size] do
    if h : i < StructuredCalls.size clauseCmd + 1 then
      codeOk := codeOk && ((code[i]?).getD .halt == originalClauseProgram.code ⟨i,h⟩)
    else codeOk := false
  let input := copyConfig (loadedLocalInput.withPC (some (Fin.ofNat _ entryNum)))
  let (fast,stats) := runInstrumented code input 180
  let source := copyConfig sourceRun180
  return codeOk && entryNum == originalClauseProgram.entry.val &&
    source.pc == fast.pc && source.registers == fast.registers &&
    source.words == fast.words && stats.executed == 180 &&
    fast.pc.isNone && BinaryArithmetic.toNat (fast.words[782]!) == 1

end IndependentNativeCost

def main : IO Unit := do
  let ok := IndependentNativeCost.smallAudit
  IO.println s!"ORIGINAL_CLAUSE_CODE_40_INSTRUCTIONS_AND_180_STEPS_FULL_STATE_EQUAL {ok}"
  unless ok do throw <| IO.userError "Original clause-count source mismatch"
