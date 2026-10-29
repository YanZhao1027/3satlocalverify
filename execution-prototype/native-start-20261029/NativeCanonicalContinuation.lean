import NativeStartLinked
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafStartup

/-! Real original `NativeLeafSetup.saveCanonical` executed immediately after
the already validated single-PC original `LeafOuterProgram.start` linker.
The saveCanonical command is the actual fixed OAI source; no parameter or
answer values are preloaded into its output stacks. This is a STAGED test,
not yet one monolithic `canonicalStart` opcode trace. -/
namespace IndependentNativeStart.Canonical
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open IndependentNativeCost
open IndependentNativeStart
open IndependentNativeStart.Linked

set_option maxRecDepth 22000

def saveCmd := NativeLeafSetup.saveCanonical

def runCanonical (fuel : Nat) : IO Unit := do
  let before ← IO.monoMsNow
  let startEntry : Fin Total := Fin.ofNat _ clEntry
  let (initial,pre) := runInstrumented linked
    (copyConfig (loadedLocalInput.withPC (some startEntry))) fuel
  let frame := takeFrame initial
  IO.println s!"NATIVE_CANONICAL_PRIOR_START halted={initial.pc.isNone} steps={pre.executed} workerClean={workerEmpty frame} stack768={BinaryArithmetic.toNat (frame.words[768]!)} stack773={BinaryArithmetic.toNat (frame.words[773]!)} stack774={BinaryArithmetic.toNat (frame.words[774]!)}"
  (← IO.getStdout).flush
  unless initial.pc.isNone && pre.executed == 6135 do
    throw <| IO.userError "Original linked outer start did not finish"
  let t0 ← IO.monoMsNow
  let table : Array (Instr 40 896 (StructuredCalls.size saveCmd + 1)) :=
    IndependentNonterminal.FastLinearize.instructionArray saveCmd
  let entry : Fin (StructuredCalls.size saveCmd + 1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry saveCmd 1 0)
  IO.println s!"NATIVE_CANONICAL_TABLE labels={table.size} sourceSites={StructuredCalls.size saveCmd} entry={entry.val} loadMs={(← IO.monoMsNow)-t0}"
  (← IO.getStdout).flush
  unless table.size == 126 do throw <| IO.userError "Original canonical stage opcode count mismatch"
  let (endC,st) := runInstrumented table (startCfg frame entry) fuel
  let endF := takeFrame endC
  let t1 ← IO.monoMsNow
  let roundsOK := endF.words[781]! == List.replicate 10 true
  let sameWords := endF.words[768]! == endF.words[780]! && endF.words[780]! == endF.words[783]!
  IO.println s!"NATIVE_CANONICAL_SAVE halted={endC.pc.isNone} executedSteps={st.executed} maxStackDataBits={st.peakTotalBits} maxSingleStack={st.peakSingleBits} canonicalValue={BinaryArithmetic.toNat (endF.words[780]!)} width={endF.words[780]!.length} denomAt817={BinaryArithmetic.toNat (endF.words[817]!)} roundsAt781={endF.words[781]!.length} allThreeWidthWordsSame={sameWords} unaryRoundsCorrect={roundsOK} workerEmpty={workerEmpty endF} finalStackBits={occupied endF} savedMs={t1-t0}"
  (← IO.getStdout).flush
  unless endC.pc.isNone && roundsOK && sameWords && workerEmpty endF &&
    BinaryArithmetic.toNat (endF.words[780]!) == 3 &&
    BinaryArithmetic.toNat (endF.words[817]!) == 1280000 &&
    BinaryArithmetic.toNat (endF.words[782]!) == 1 do
      throw <| IO.userError "Genuine saveCanonical stage failed expected arithmetic invariants"
  IO.println s!"NATIVE_CANONICAL_STAGED_PASS totalIncludingSeparateHalts={pre.executed+st.executed} allStagesPhysical=true executionMs={(← IO.monoMsNow)-before}"
  (← IO.getStdout).flush

end IndependentNativeStart.Canonical
