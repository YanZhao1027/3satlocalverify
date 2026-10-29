import PhysicalNumericLift

namespace IndependentNativeCost.PhysicalStream
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-! Independent every-step scan of ALL 896 physical stacks; checks the
incremental source bit accounting, not full solver correctness. -/
def checkPhysicalEveryStepNumeric (table : Array (Instr 16 44 L))
    (start : CompactState L) (fuel : Nat) : Bool := Id.run do
  let mut c := start
  let mut peak := recount c.words
  let mut peakSingle := c.words.foldl (fun n w => max n w.length) 0
  let mut executed := 0
  for _ in [:fuel] do
    let some pc := c.pc | break
    let some op := table[pc.val]? | return false
    c := physicalNumericOne op c
    executed := executed + 1
    peak := max peak (recount c.words)
    peakSingle := max peakSingle (c.words.foldl (fun n w => max n w.length) 0)
  let (final,stat) := runFast table start fuel
  return final.pc == c.pc && final.registers == c.registers &&
    final.words == c.words && stat.executed == executed &&
    stat.peakTotalBits == peak && stat.peakSingleBits == peakSingle &&
    stat.finalTotalBits == recount c.words

/-- First a real physical nonempty formula -> original ClauseCount.caller;
then original HashParametersProgram.ABI.command with actual registers/stack
mapping used by original LeafProgram.HashParameters.command. -/
def measureNumeric (fuel : Nat) (checkEveryStep : Bool) : IO Unit := do
  let begin ← IO.monoMsNow
  let clauseCmd := LeafProgram.ClauseCount.caller
  let clauseTable : Array (Instr 40 896 (StructuredCalls.size clauseCmd + 1)) :=
    IndependentNonterminal.Linearize.instructionArray clauseCmd
  let clauseEntry : Fin (StructuredCalls.size clauseCmd+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry clauseCmd 1 0)
  let (clauseEnd,clauseCost) := runInstrumented clauseTable
    (copyConfig (loadedLocalInput.withPC (some clauseEntry))) fuel
  IO.println s!"REAL_PHYSICAL_NUMERIC_CLAUSE halted={clauseEnd.pc.isNone} steps={clauseCost.executed} count={BinaryArithmetic.toNat (clauseEnd.words[782]!)} peakDataBits={clauseCost.peakTotalBits}"
  (← IO.getStdout).flush
  unless clauseEnd.pc.isNone && clauseCost.executed == 180 &&
    BinaryArithmetic.toNat (clauseEnd.words[782]!) == 1 do
    throw <| IO.userError "Original clause counter failed"
  let tableStart ← IO.monoMsNow
  let table : Array (Instr 16 44 L) :=
    IndependentNonterminal.Linearize.instructionArray Cmd
  IO.println s!"ORIGINAL_NUMERIC_ABI_SOURCE_TABLE size={table.size} expected={L} materialize_ms={(← IO.monoMsNow)-tableStart}"
  (← IO.getStdout).flush
  unless table.size == L do throw <| IO.userError "Incorrect ABI source table size"
  let input : CompactState L :=
    {pc := some sourceEntry, registers := clauseEnd.registers, words := clauseEnd.words}
  let startExec ← IO.monoMsNow
  IO.println s!"NUMERIC_BEFORE_FAST pc={input.pc.map Fin.val} inputRegs={input.registers.size} inputStacks={input.words.size} firstLabel={sourceEntry.val}"
  (← IO.getStdout).flush
  let (done,st) := runFast table input fuel
  let ended ← IO.monoMsNow
  IO.println s!"REAL_PHYSICAL_NUMERIC_HASH halted={done.pc.isNone} stepsABI={st.executed} stepsWithOuterHalt={st.executed+1} peakTotalStackBits={st.peakTotalBits} peakSingleStackBits={st.peakSingleBits} initialDataBits={st.initialBits} finalDataBits={st.finalTotalBits} recountedFinalBits={recount done.words} sourceLabelsVisited={st.visitedDistinctLabels} instruction_ms={ended-startExec}"
  (← IO.getStdout).flush
  IO.println s!"REAL_PHYSICAL_NUMERIC_OUTPUT m={BinaryArithmetic.toNat (done.words[782]!)} alpha={BinaryArithmetic.toNat (done.words[768]!)} distanceDenom={BinaryArithmetic.toNat (done.words[773]!)} loopCap={BinaryArithmetic.toNat (done.words[774]!)} n={BinaryArithmetic.toNat (done.words[785]!)} B={BinaryArithmetic.toNat (done.words[786]!)}"
  (← IO.getStdout).flush
  let sourceStart : CompactState L := {(project clauseEnd.registers clauseEnd.words) with pc := some sourceEntry}
  let (sourceEnd,sourceCost) := runInstrumented table sourceStart fuel
  let projectedEnd := project done.registers done.words
  let sourceMatch := done.pc == sourceEnd.pc &&
    projectedEnd.registers == sourceEnd.registers &&
    projectedEnd.words == sourceEnd.words && st.executed == sourceCost.executed
  let frameMatch := allUnmappedPreserved clauseEnd.registers done.registers clauseEnd.words done.words
  IO.println s!"REAL_PHYSICAL_NUMERIC_AUDIT ABI_steps={sourceCost.executed} ABI_original_state_match={sourceMatch} unmapped40x896_frame_preserved={frameMatch} raw_total_steps={clauseCost.executed+st.executed+1}"
  (← IO.getStdout).flush
  if checkEveryStep then
    let recomputed := checkPhysicalEveryStepNumeric table input fuel
    IO.println s!"REAL_PHYSICAL_NUMERIC_EVERY_STEP_SPACE_CHECK equal={recomputed}"
    (← IO.getStdout).flush
    unless recomputed do throw <| IO.userError "Physical stack-space mismatch"
  IO.println s!"REAL_PHYSICAL_NUMERIC_RUN wall_internal_ms={ended-begin}"
  (← IO.getStdout).flush
  unless done.pc.isNone && st.executed==3585 && sourceMatch && frameMatch &&
      st.finalTotalBits == recount done.words &&
      BinaryArithmetic.toNat (done.words[768]!)==3 &&
      BinaryArithmetic.toNat (done.words[773]!)==1280000 &&
      BinaryArithmetic.toNat (done.words[774]!)==10 do
    throw <| IO.userError "Actual mapped original hash command did not finish or disagreed"


end IndependentNativeCost.PhysicalStream

def main (args : List String) : IO Unit := do
  let fuel := (args[0]?.bind String.toNat?).getD 15000
  let verify := args[1]?.getD "no" == "verify"
  IndependentNativeCost.PhysicalStream.measureNumeric fuel verify
