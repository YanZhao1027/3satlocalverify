import CompactNative40
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHashParameters

/-! Source-level physical 40×896 leaf-bank experiment. The *same* real
one-positive-unit-clause CNF is used. Stage 1 executes the original clause
counter. Stage 2 consumes the exact resulting physical machine state and
executes ORIGINAL LeafProgram.HashParameters.command with its exact 40x896
ported register and stack mappings. NO precomputed clause count or hash
outputs are injected: values carry over through actual source instructions.
The separate unexecuted `clearWorker` and `saveWidth` suffixes are excluded. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 18000
set_option maxHeartbeats 900000

private def stateFromCompact {l : Nat} (c : CompactState l) : StructuredCalls.State 40 896 :=
  ⟨fun i => c.registers[i.val]!, fun i => c.words[i.val]!⟩

def runPhysical (fuel : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let code1 : Array (Instr 40 896 (StructuredCalls.size LeafProgram.ClauseCount.caller+1)) :=
    IndependentNonterminal.Linearize.instructionArray LeafProgram.ClauseCount.caller
  let entry1 : Fin (StructuredCalls.size LeafProgram.ClauseCount.caller+1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry LeafProgram.ClauseCount.caller 1 0)
  let (afterClause,cost1) := runInstrumented code1
    (copyConfig (loadedLocalInput.withPC (some entry1))) fuel
  let firstStop ← IO.monoMsNow
  IO.println s!"PHYSICAL_CLAUSE completed={afterClause.pc.isNone} steps={cost1.executed} peakStackBits={cost1.peakTotalBits} resultingM={BinaryArithmetic.toNat (afterClause.words[782]!)}"
  unless afterClause.pc.isNone && BinaryArithmetic.toNat (afterClause.words[782]!)==1 do
    throw <| IO.userError "Physical clause stage not complete"
  let cmd2 := LeafProgram.HashParameters.command
  let code2 : Array (Instr 40 896 (StructuredCalls.size cmd2+1)) :=
    IndependentNonterminal.Linearize.instructionArray cmd2
  let entry2 : Fin (StructuredCalls.size cmd2+1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry cmd2 1 0)
  let middle ← IO.monoMsNow
  IO.println s!"PHYSICAL_HASH_TABLE staticSites={code2.size} entry={entry2.val} build_ms={middle-firstStop}"
  let input2 := stateFromCompact afterClause
  let (afterHash,cost2) := runInstrumented code2
    (copyConfig (input2.withPC (some entry2))) fuel
  let endTime ← IO.monoMsNow
  let trueFinal := afterHash.words.foldl (fun n w => n+w.length) 0
  IO.println s!"PHYSICAL_HASH_STAGE halted={afterHash.pc.isNone} steps={cost2.executed} peakStackBits={cost2.peakTotalBits} peakSingleBits={cost2.peakSingleBits} finalStackBits={cost2.finalTotalBits} recalculatedFinal={trueFinal} distinctiveSites={cost2.visitedDistinctLabels} execution_ms={endTime-middle}"
  IO.println s!"PHYSICAL_HASH_OUTPUT numClauses={BinaryArithmetic.toNat (afterHash.words[782]!)} alphabet={BinaryArithmetic.toNat (afterHash.words[768]!)} distanceDenom={BinaryArithmetic.toNat (afterHash.words[773]!)} loopCap={BinaryArithmetic.toNat (afterHash.words[774]!)} rows={BinaryArithmetic.toNat (afterHash.words[777]!)} ambientN={BinaryArithmetic.toNat (afterHash.words[785]!)} boundB={BinaryArithmetic.toNat (afterHash.words[786]!)}"
  IO.println s!"PHYSICAL_TWO_STAGE_TOTAL sourceInstructionsIncludingBothHalts={cost1.executed+cost2.executed} peakStackBits={max cost1.peakTotalBits cost2.peakTotalBits} full_two_stages_ms={endTime-t0}"
  unless afterHash.pc.isNone && trueFinal==cost2.finalTotalBits &&
    BinaryArithmetic.toNat (afterHash.words[768]!)==3 &&
    BinaryArithmetic.toNat (afterHash.words[773]!)==1280000 &&
    BinaryArithmetic.toNat (afterHash.words[774]!)==10 do
      throw <| IO.userError "Physical 40×896 source stages incorrect"

end IndependentNativeCost

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 50000
  IndependentNativeCost.runPhysical fuel
