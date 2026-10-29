import PhysicalNumericLift
import FastLinearizedCompiler
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCode

/-! Run original SAT native outer-start stages on the same 40-register,
896-stack physical data bank: original ClauseCount, original 16x44 ABI
relocated with kernel-proven original port maps, original Wide cleanup
(40x768 identity), and original saveWidth route from 768 to 783.

STAGED execution: each original command's separate terminal HALT is counted
independently. The source-level monolithic `LeafOuterProgram.start` is not
claimed to have been executed by a single compiled program. -/
namespace IndependentNativeStart
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open IndependentNativeCost
open IndependentNativeCost.PhysicalStream

set_option maxRecDepth 22000
set_option maxHeartbeats 1200000

structure Frame where
  regs : Array Bool
  words : Array (List Bool)

def takeFrame (c : CompactState l) : Frame := ⟨c.registers, c.words⟩
def startCfg (f : Frame) (e : Fin l) : CompactState l :=
  ⟨some e, f.regs, f.words⟩

def occupied (f : Frame) : Nat := f.words.foldl (fun acc w => acc + w.length) 0

def workerBits (f : Frame) : Nat := Id.run do
  let mut n := 0
  for i in [:768] do n := n + (f.words[i]!).length
  return n

def workerEmpty (f : Frame) : Bool := Id.run do
  for i in [:768] do
    unless (f.words[i]!).isEmpty do return false
  return true

def allRegsClear (f : Frame) : Bool := f.regs.all (fun b => !b)

def preservedUpper (a b : Frame) : Bool := Id.run do
  for i in [768:896] do
    unless a.words[i]! == b.words[i]! do return false
  return true

def runStages (fuel : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let c0 := LeafProgram.ClauseCount.caller
  let p0 : Array (Instr 40 896 (StructuredCalls.size c0 + 1)) :=
    IndependentNonterminal.Linearize.instructionArray c0
  let e0 : Fin (StructuredCalls.size c0 + 1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry c0 1 0)
  let (f0,s0) := runInstrumented p0
    (copyConfig (loadedLocalInput.withPC (some e0))) fuel
  let frame0 := takeFrame f0
  IO.println s!"NATIVE_STAGE_CLAUSE halted={f0.pc.isNone} steps={s0.executed} m={BinaryArithmetic.toNat (frame0.words[782]!)} peakBits={s0.peakTotalBits} outputBytes={occupied frame0}"
  (← IO.getStdout).flush
  unless f0.pc.isNone && s0.executed == 180 && BinaryArithmetic.toNat (frame0.words[782]!) == 1 do
    throw <| IO.userError "Authentic original clause counting failed"

  let c1 := HashParametersProgram.ABI.command
  let p1 : Array (Instr 16 44 (StructuredCalls.size c1 + 1)) :=
    IndependentNonterminal.Linearize.instructionArray c1
  let e1 : Fin (StructuredCalls.size c1 + 1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry c1 1 0)
  let (f1,s1) := runFast p1 (startCfg frame0 e1) fuel
  let frame1 := takeFrame f1
  IO.println s!"NATIVE_STAGE_HASH halted={f1.pc.isNone} steps={s1.executed} alpha={BinaryArithmetic.toNat (frame1.words[768]!)} denominator={BinaryArithmetic.toNat (frame1.words[773]!)} cap={BinaryArithmetic.toNat (frame1.words[774]!)} peakBits={s1.peakTotalBits} workerBits={workerBits frame1} totalBits={occupied frame1}"
  (← IO.getStdout).flush
  unless f1.pc.isNone && s1.executed == 3585 &&
    BinaryArithmetic.toNat (frame1.words[768]!) == 3 &&
    BinaryArithmetic.toNat (frame1.words[773]!) == 1280000 &&
    BinaryArithmetic.toNat (frame1.words[774]!) == 10 do
    throw <| IO.userError "Original hash stage incorrect or failed to terminate"

  let c2 := LeafProgram.Cleanup.Wide.command
  let e2 : Fin (StructuredCalls.size c2 + 1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry c2 1 0)
  let prepareCleanup ← IO.monoMsNow
  IO.println s!"NATIVE_STAGE_CLEANUP_PREPARING originalCodeSites={StructuredCalls.size c2} fuel={fuel} workerInitialBits={workerBits frame1} tmpStack767Empty={(frame1.words[767]!).isEmpty}"
  (← IO.getStdout).flush
  unless (frame1.words[767]!).isEmpty do throw <| IO.userError "Original cleanup required empty scratch stack767"
  let p2 : Array (Instr 40 768 (StructuredCalls.size c2 + 1)) :=
    IndependentNonterminal.FastLinearize.instructionArray c2
  let afterTable ← IO.monoMsNow
  IO.println s!"NATIVE_STAGE_CLEANUP_CODE built={p2.size} expected={StructuredCalls.size c2+1} tableMs={afterTable-prepareCleanup}"
  (← IO.getStdout).flush
  unless p2.size == StructuredCalls.size c2+1 do
    throw <| IO.userError "Original cleanup instruction table size incorrect"
  let (f2,s2) := runInstrumented p2 (startCfg frame1 e2) fuel
  let frame2 := takeFrame f2
  let observedCleanup := 2 * workerBits frame1 + 2348
  IO.println s!"NATIVE_STAGE_CLEANUP halted={f2.pc.isNone} steps={s2.executed} expectedOriginalSteps={observedCleanup} peakBits={s2.peakTotalBits} all40RegsBlank={allRegsClear frame2} all768WorkerStacksBlank={workerEmpty frame2} upper128Preserved={preservedUpper frame1 frame2} outputBits={occupied frame2}"
  (← IO.getStdout).flush
  unless f2.pc.isNone && s2.executed == observedCleanup &&
    workerEmpty frame2 && allRegsClear frame2 && preservedUpper frame1 frame2 do
      throw <| IO.userError "Original 768 worker stacks cleanup inaccurate or failed"

  let c3 := saveWidth
  let p3 : Array (Instr 40 896 (StructuredCalls.size c3 + 1)) :=
    IndependentNonterminal.FastLinearize.instructionArray c3
  let e3 : Fin (StructuredCalls.size c3 + 1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry c3 1 0)
  let (f3,s3) := runInstrumented p3 (startCfg frame2 e3) fuel
  let frame3 := takeFrame f3
  let expectedRoute := 2 * (frame2.words[783]!).length +
    7 * (frame2.words[768]!).length + 9
  IO.println s!"NATIVE_STAGE_SAVE_WIDTH halted={f3.pc.isNone} steps={s3.executed} expectedOriginalSteps={expectedRoute} peakBits={s3.peakTotalBits} source768={(frame3.words[768]!).length} dest783={(frame3.words[783]!).length} copiedExactly={frame3.words[783]! == frame3.words[768]!} totalBits={occupied frame3}"
  (← IO.getStdout).flush
  unless f3.pc.isNone && s3.executed == expectedRoute &&
    frame3.words[783]! == frame3.words[768]! &&
    workerEmpty frame3 && preservedUpper frame2 frame3 == false do
    -- upper128 includes destination stack783, so inequality is expected.
    throw <| IO.userError "Original saveWidth route failed or did not write output"
  let t1 ← IO.monoMsNow
  IO.println s!"NATIVE_START_STAGED_PASS halted=true sourceStepSumIncludingFourIndividualHalts={s0.executed+s1.executed+s2.executed+s3.executed} maxStackDataBitsAcrossStages={max s0.peakTotalBits (max s1.peakTotalBits (max s2.peakTotalBits s3.peakTotalBits))} finalSource768={BinaryArithmetic.toNat (frame3.words[768]!)} output783={BinaryArithmetic.toNat (frame3.words[783]!)} internalWallMs={t1-t0}"
  (← IO.getStdout).flush

end IndependentNativeStart
