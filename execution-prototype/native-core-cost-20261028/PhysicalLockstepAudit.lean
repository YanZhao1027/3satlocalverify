import PhysicalNumericLift

/-! FAIL-CLOSED exhaustive per-executed-instruction audit for the true
40x896 mapped leaf hash ABI: compare all 3585 steps to an independent 16x44
source interpreter and recount the entire 896-stack store at EVERY step.
The source opcode table has been separately compared to the original upstream
BitProgram.program.code, 637/637, in HashABISourceAudit.lean. -/

namespace IndependentNativeCost.PhysicalStream
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog

set_option maxRecDepth 18000

def runLockstep (fuel : Nat) : IO Unit := do
  let c := LeafProgram.ClauseCount.caller
  let clauseTable : Array (Instr 40 896 (StructuredCalls.size c+1)) :=
    IndependentNonterminal.Linearize.instructionArray c
  let ce : Fin (StructuredCalls.size c+1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry c 1 0)
  let (afterClause, stClause) := runInstrumented clauseTable
    (copyConfig (loadedLocalInput.withPC (some ce))) 15000
  unless afterClause.pc.isNone && stClause.executed == 180 &&
    BinaryArithmetic.toNat (afterClause.words[782]!) == 1 do
      throw <| IO.userError "Original CNF clause-count stage did not finish"
  let table : Array (Instr 16 44 L) :=
    IndependentNonterminal.Linearize.instructionArray Cmd
  unless table.size == 637 do throw <| IO.userError "Bad ABI opcode table"
  let input : CompactState L :=
    {pc:=some sourceEntry, registers:=afterClause.registers, words:=afterClause.words}
  let virtualInput := {(project afterClause.registers afterClause.words) with pc:=some sourceEntry}
  let mut phys := input
  let mut virt := virtualInput
  let mut peak := recount phys.words
  let mut peakSingle := phys.words.foldl (fun a w => max a w.length) 0
  let mut observedSteps := 0
  for _ in [:fuel] do
    let some pc := phys.pc | break
    let some opcode := table[pc.val]? | throw <| IO.userError "Undefined source label"
    phys := physicalNumericOne opcode phys
    virt := runOne opcode virt
    observedSteps := observedSteps + 1
    let projected := project phys.registers phys.words
    unless phys.pc == virt.pc && projected.registers == virt.registers &&
        projected.words == virt.words do
      throw <| IO.userError s!"Physical machine and original 16x44 ABI diverge at step {observedSteps}"
    peak := max peak (recount phys.words)
    peakSingle := max peakSingle (phys.words.foldl (fun a w => max a w.length) 0)
  let (fast,stats) := runFast table input fuel
  let result := phys.pc.isNone && virt.pc.isNone && observedSteps == 3585 &&
    phys.pc == fast.pc && phys.registers == fast.registers && phys.words == fast.words &&
    stats.executed == observedSteps && stats.peakTotalBits == peak &&
    stats.peakSingleBits == peakSingle && stats.finalTotalBits == recount phys.words &&
    allUnmappedPreserved afterClause.registers phys.registers afterClause.words phys.words &&
    BinaryArithmetic.toNat (phys.words[768]!) == 3 &&
    BinaryArithmetic.toNat (phys.words[773]!) == 1280000 &&
    BinaryArithmetic.toNat (phys.words[774]!) == 10
  IO.println s!"PHYSICAL_LOCKSTEP_AUDIT everyStepMatched={result} steps={observedSteps} sourceLabels={table.size} physicalRegs={phys.registers.size} physicalStacks={phys.words.size} occupiedStackPeak={peak} maxSingleStack={peakSingle} output3m={BinaryArithmetic.toNat (phys.words[768]!)} outputDenom={BinaryArithmetic.toNat (phys.words[773]!)} outputLoopCap={BinaryArithmetic.toNat (phys.words[774]!)}"
  unless result do throw <| IO.userError "Full 3585-step original/physical state and stack accounting failed"

end IndependentNativeCost.PhysicalStream

def main : IO Unit := IndependentNativeCost.PhysicalStream.runLockstep 12000
