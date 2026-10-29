import NativeCanonicalContinuation

/-! One-PC, one-HALT executable bit trace of original NativeLeafSetup.canonicalStart
= .seq LeafOuterProgram.start saveCanonical; constructed by relocating the
already audited original start opcode table and genuine saveCanonical command
code. Compare all physical state at the single cross-command boundary.

Independent linking is not a global formal equality proof to upstream
`StructuredCalls.compiled NativeLeafSetup.canonicalStart` for all sites. -/
namespace IndependentNativeStart.CanonicalLinked
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open IndependentNativeCost
open IndependentNativeStart
open IndependentNativeStart.Linked

set_option maxRecDepth 24000

abbrev Full : Nat := 3161
abbrev Start : Nat := 3036
abbrev Additional : Nat := 126

def afterStartBase : Nat := 3035

def sourceSave : Array (Instr 40 896 Additional) :=
  IndependentNonterminal.FastLinearize.instructionArray NativeLeafSetup.saveCanonical

def additionalEntry : Nat :=
  IndependentNonterminal.Linearize.callEntry NativeLeafSetup.saveCanonical 1 0

private def place (n : Nat) : Fin Full := Fin.ofNat _ n

/-- Every original opcode is moved only by label relocation; data source
and register/stack addresses stay untouched. -/
def appendStage (source : Array (Instr 40 896 n)) (base next : Nat) :
    Array (Instr 40 896 Full) := Id.run do
  let mut result := #[]
  for i in [1:source.size] do
    let op := (source[i]?).getD Instr.halt
    result := result.push <| ProgramLinking.relocateInstr id id
      (fun pc : Fin n => place (if pc.val==0 then next else base+pc.val))
      (some (place next)) op
  return result

def monolithic : Array (Instr 40 896 Full) := Id.run do
  let mut code : Array (Instr 40 896 Full) := #[Instr.halt]
  code := code ++ appendStage linked 0 (afterStartBase+additionalEntry)
  code := code ++ appendStage sourceSave afterStartBase 0
  return code

def runMonolithic (fuel : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let code := monolithic
  IO.println s!"ORIGINAL_CANONICAL_CODE linkedLabels={code.size} originalSitesExpected=3160 startBody=3035 saveBody=125 entry=3 extraEntry={additionalEntry}"
  (← IO.getStdout).flush
  unless code.size == Full && code.size==3161 &&
    sourceSave.size==126 && additionalEntry==1 do
      throw <| IO.userError "Source code table size or entry mismatched"
  let entry : Fin Full := Fin.ofNat _ clEntry
  let (finish,stats) := runInstrumented code
    (copyConfig (loadedLocalInput.withPC (some entry))) fuel
  let frame := takeFrame finish
  let canonicalOK := frame.words[768]! == frame.words[780]! &&
    frame.words[780]! == frame.words[783]! &&
    frame.words[781]! == List.replicate 10 true
  IO.println s!"ORIGINAL_CANONICAL_SINGLE halted={finish.pc.isNone} executedSteps={stats.executed} allStackDataPeak={stats.peakTotalBits} longestStack={stats.peakSingleBits} staticLabels={code.size} executedDistinctLabels={stats.visitedDistinctLabels} initialBits={stats.initialBits} finalBits={stats.finalTotalBits} recountedFinal={occupied frame} workerClean={workerEmpty frame} allRegsClear={allRegsClear frame}"
  IO.println s!"ORIGINAL_CANONICAL_OUTPUT clauses={BinaryArithmetic.toNat (frame.words[782]!)} modulus={BinaryArithmetic.toNat (frame.words[780]!)} canonicalWidth={frame.words[780]!.length} distanceDenom={BinaryArithmetic.toNat (frame.words[817]!)} unaryRoundCount={frame.words[781]!.length} sourceWidthSame={canonicalOK}"
  IO.println s!"ORIGINAL_CANONICAL_TIME internalMs={(← IO.monoMsNow)-t0}"
  (← IO.getStdout).flush
  unless finish.pc.isNone && stats.executed == 7085 &&
    stats.peakTotalBits == 125 && stats.finalTotalBits == occupied frame &&
    workerEmpty frame && canonicalOK &&
    BinaryArithmetic.toNat (frame.words[782]!)==1 &&
    BinaryArithmetic.toNat (frame.words[780]!)==3 &&
    BinaryArithmetic.toNat (frame.words[817]!)==1280000 do
    throw <| IO.userError "Native canonical single program unsuccessful"
  IO.println "ORIGINAL_CANONICAL_SINGLE_PROGRAM_PASS -- no HighQuery or #SAT counting"

end IndependentNativeStart.CanonicalLinked
