import CompactNative40

namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

/-- The original source Cmd parameter is copied into exactly its `Instr`
array; use the structurally computed entry instead of repeatedly reducing
the massive dependent-site equivalence at runtime. This relocation still
requires a separately verified compiler-refinement check. -/
def measure (name : String) (c : StructuredCalls.Cmd 40 896)
    (fuel : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let table : Array (Instr 40 896 (StructuredCalls.size c + 1)) :=
    IndependentNonterminal.Linearize.instructionArray c
  let entryNum := IndependentNonterminal.Linearize.callEntry c 1 0
  let entry : Fin (StructuredCalls.size c + 1) := Fin.ofNat _ entryNum
  let input := copyConfig (loadedLocalInput.withPC (some entry))
  let startBits := loadedInputBits
  IO.println s!"STAGE_SETUP name={name} codeSize={table.size} entry={entryNum} initialBits={startBits} fuel={fuel}"
  let t1 ← IO.monoMsNow
  let (finish,stats) := runInstrumented table input fuel
  let t2 ← IO.monoMsNow
  let realFinalBits := finish.words.foldl (fun sum st => sum + st.length) 0
  IO.println s!"STAGE_RESULT name={name} halted={finish.pc.isNone} steps={stats.executed} initialStackBits={stats.initialBits} peakStackBits={stats.peakTotalBits} peakSingle={stats.peakSingleBits} finalStackBits={stats.finalTotalBits} recountedFinal={realFinalBits} distinctSourcePC={stats.visitedDistinctLabels} sets={stats.set} copies={stats.copy} logic={stats.bitLogic} tests={stats.tests} pushes={stats.push} pops={stats.pop} peeks={stats.peek} jumps={stats.goto} halts={stats.halt} materialize_ms={t1-t0} execution_ms={t2-t1}"
  IO.println s!"STAGE_REGISTERS name={name} countPort782={BinaryArithmetic.toNat (finish.words[782]!)} hashModPort780={BinaryArithmetic.toNat (finish.words[780]!)} depthPort817={BinaryArithmetic.toNat (finish.words[817]!)} roundLength781={(finish.words[781]!).length} input785={BinaryArithmetic.toNat (finish.words[785]!)} input786={BinaryArithmetic.toNat (finish.words[786]!)}"
  unless stats.executed == stats.set+stats.copy+stats.bitLogic+stats.tests+stats.push+stats.pop+stats.peek+stats.goto+stats.halt do
    throw <| IO.userError "Opcode subtype counter mismatch"
  unless realFinalBits == stats.finalTotalBits do
    throw <| IO.userError "Final occupied-bit count mismatch"

end IndependentNativeCost

def main (args : List String) : IO Unit := do
  let stage := args[0]?.getD "clause"
  let fuel := (args[1]?.bind String.toNat?).getD 30000
  if stage == "clause" then
    IndependentNativeCost.measure "clauseCount" OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount.caller fuel
  else if stage == "start" then
    IndependentNativeCost.measure "originalStart" OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.start fuel
  else if stage == "canonical" then
    IndependentNativeCost.measure "canonicalStart" OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalStart fuel
  else
    throw <| IO.userError "Select clause / start / canonical"
