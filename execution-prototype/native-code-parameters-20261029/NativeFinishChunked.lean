import NativeFinishSuffixProbe

/-! Real original OAI `NativeLeafPreparation.afterCode` BitProgram, chunked
for progress and hard resource caps. Each chunk starts with EXACT previous
physical state and source PC. No result is injected. This is real source
execution, NOT an asymptotic proof. The original zero candidate may need
millions of paid bit instructions even for m=1,B=8. -/
namespace IndependentNativeParameters.FinishChunked
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeParameters.Physical

set_option maxRecDepth 23000

def run (chunkSize chunks : Nat) : IO Unit := do
  let begin ← IO.monoMsNow
  let ready ← IndependentNativeParameters.Serializer.runSerializer 180000
  let cmd := NativeLeafPreparation.afterCode
  let table := IndependentNonterminal.FastLinearize.instructionArray cmd
  let entry : Fin (StructuredCalls.size cmd+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry cmd 1 0)
  IO.println s!"CHUNKED_ORIGINAL_FINISH_START codeLabels={table.size} fuelPerChunk={chunkSize} maxChunks={chunks} depth={BinaryArithmetic.toNat (ready.words[817]!)} digitWidth={(ready.words[780]!).length} initialRow777Bits={(ready.words[777]!).length}"
  (← IO.getStdout).flush
  let mut current := inject ready entry
  let mut actualSteps := 0
  let mut maxBits := bits ready
  let mut maxSingle := 0
  for k in [:chunks] do
    let chunkStart ← IO.monoMsNow
    let (next,stats) := runInstrumented table current chunkSize
    current := next
    actualSteps := actualSteps+stats.executed
    maxBits := max maxBits stats.peakTotalBits
    maxSingle := max maxSingle stats.peakSingleBits
    let dataLen := (current.words[778]!).length
    let runtime := (← IO.monoMsNow)-chunkStart
    IO.println s!"CHUNKED_ORIGINAL_FINISH_PROGRESS chunk={k+1} accumulatedSourceSteps={actualSteps} halted={current.pc.isNone} sourcePC={current.pc.map Fin.val} generatedZeroWordBits={dataLen} occupiedDataPeak={maxBits} longestStack={maxSingle} sourceChunkMs={runtime}"
    (← IO.getStdout).flush
    if current.pc.isNone then break
  let totalTime := (← IO.monoMsNow)-begin
  let result := bank current
  let inputPreserved := current.words[777]! == ready.words[777]!
  let originalData : LeafOuterProgram.Data :=
    ⟨fun i => ready.regs[i.val]!, fun i => ready.words[i.val]!⟩
  let expected := HashGreedyProgram.Initialize.zeroWord originalData
  let exact := if current.pc.isNone then current.words[778]! == expected else false
  IO.println s!"CHUNKED_ORIGINAL_FINISH_RESULT halted={current.pc.isNone} actualInstructions={actualSteps} sourceLabels={table.size} zeroWordLen={(current.words[778]!).length} theoreticalZeroWordLen={expected.length} exactOriginalZeroWord={exact} sourceSerializedRowsPreserved={inputPreserved} finishedDataBits={bits result} peakDataBits={maxBits} maximumSingleStack={maxSingle} totalInternalMs={totalTime}"
  (← IO.getStdout).flush
  unless inputPreserved do throw <| IO.userError "Original finish changed serialized rows"
  if current.pc.isNone && !exact then
    throw <| IO.userError "Original suffix halted with incorrect zero candidate"

end IndependentNativeParameters.FinishChunked
