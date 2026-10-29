import NativeTwoSearchStages
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

/-! NativeCodeAssembly.serialize, ACTUAL original bit program on the real
physical 40x896 state produced by real CodeParametersProgram + both searches.
Includes original row input routing, original CodeRowsProgram.command, actual
output 12->777 routing and entire original 768-stack worker cleanup.
No row is precomputed or injected. No high-query / final #SAT solver. -/
namespace IndependentNativeParameters.Serializer
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeParameters.Physical
open IndependentNativeParameters.TwoSearches

set_option maxRecDepth 22000

abbrev RowCmd := CodeRowsProgram.command
abbrev RowLabels : Nat := StructuredCalls.size RowCmd+1

def rowSource : Array (Instr 16 64 RowLabels) :=
  IndependentNonterminal.Linearize.instructionArray RowCmd

def rowPhysical : Array (Instr 40 896 RowLabels) :=
  rowSource.map (fun op => ProgramLinking.relocateInstr regs16 stacks64 id none op)

def localView (b : Bank) (e : Fin RowLabels) : CompactState RowLabels :=
  ⟨some e, Array.ofFn (fun i : Fin 16 => b.regs[i.val]!),
   Array.ofFn (fun i : Fin 64 => b.words[i.val]!)⟩

def viewEquals (b : Bank) (localResult : CompactState RowLabels) : Bool :=
  localResult.registers == Array.ofFn (fun i : Fin 16 => b.regs[i.val]!) &&
  localResult.words == Array.ofFn (fun i : Fin 64 => b.words[i.val]!)

def runSerializer (fuel : Nat) : IO Bank := do
  let t0 ← IO.monoMsNow
  let ready ← IndependentNativeParameters.TwoSearches.run fuel
  IO.println s!"SERIALIZER_REAL_INPUT codeD={BinaryArithmetic.toNat (ready.words[801]!)} graphMatrix816Bits={(ready.words[816]!).length} localMatrix815Bits={(ready.words[815]!).length} actualInputDataBits={bits ready}"
  (← IO.getStdout).flush

  let inCmd := routes NativeCodeAssembly.rowInputs
  let inCode := IndependentNonterminal.Linearize.instructionArray inCmd
  let inEntry : Fin (StructuredCalls.size inCmd+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry inCmd 1 0)
  let (routed,costIn) := runInstrumented inCode (inject ready inEntry) fuel
  IO.println s!"SERIALIZER_INPUT_ROUTE halted={routed.pc.isNone} steps={costIn.executed} sourceLabels={inCode.size} inputWidth={(routed.words[5]!).length} graphWord9={(routed.words[9]!).length} localWord10={(routed.words[10]!).length}"
  (← IO.getStdout).flush
  unless routed.pc.isNone do throw <| IO.userError "Original serializer input routing failed"

  let code := rowPhysical
  let entry : Fin RowLabels := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry RowCmd 1 0)
  IO.println s!"SERIALIZER_REAL_ROW_SOURCE sourceLabels={rowSource.size} mappedLabels={code.size} entry={entry.val} fuel={fuel}"
  (← IO.getStdout).flush
  let (raw,costCore) := runInstrumented code (inject (bank routed) entry) fuel
  let (ref,refCost) := runInstrumented rowSource (localView (bank routed) entry) fuel
  let localAgrees := ref.pc == raw.pc && costCore.executed==refCost.executed &&
    viewEquals (bank raw) ref
  IO.println s!"SERIALIZER_REAL_ROW_CORE halted={raw.pc.isNone} executedSteps={costCore.executed} peakStackBits={costCore.peakTotalBits} visitedSourceLabels={costCore.visitedDistinctLabels} outputRowBits={(raw.words[12]!).length} original16x64StateEqualsPhysical={localAgrees}"
  (← IO.getStdout).flush
  unless raw.pc.isNone && localAgrees do throw <| IO.userError "Original physical CodeRowsProgram source diverged"

  let outCmd := routes NativeCodeAssembly.rowOutputs
  let outCode := IndependentNonterminal.Linearize.instructionArray outCmd
  let outEntry : Fin (StructuredCalls.size outCmd+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry outCmd 1 0)
  let (saved,costOut) := runInstrumented outCode (inject (bank raw) outEntry) fuel
  let savedMatches := saved.words[777]! == raw.words[12]!
  IO.println s!"SERIALIZER_ORIGINAL_OUTPUT_ROUTE halted={saved.pc.isNone} executedSteps={costOut.executed} rowSavedTo777={savedMatches} persistedRowBits={(saved.words[777]!).length}"
  (← IO.getStdout).flush
  unless saved.pc.isNone && savedMatches do throw <| IO.userError "Original serializer result was not saved"

  let clearCmd := LeafProgram.Cleanup.Wide.command
  let clearCode := IndependentNonterminal.FastLinearize.instructionArray clearCmd
  let clearEntry : Fin (StructuredCalls.size clearCmd+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry clearCmd 1 0)
  let (done,costClear) := runInstrumented clearCode (inject (bank saved) clearEntry) fuel
  let final := bank done
  let retained := final.words[777]! == saved.words[777]! &&
    final.words[815]! == ready.words[815]! && final.words[816]! == ready.words[816]!
  let expectedClear := 2*(List.range 768).foldl (fun n i => n+(saved.words[i]!).length) 0+2348
  IO.println s!"SERIALIZER_FINAL_CLEANUP halted={done.pc.isNone} steps={costClear.executed} expectedOriginalBudget={expectedClear} all768WorkerStacksEmpty={workerClean final} allRegistersZero={final.regs.all (fun v=>!v)} rowAndBothMatricesPersist={retained} row777Bits={(final.words[777]!).length} finalDataBits={bits final}"
  (← IO.getStdout).flush
  unless done.pc.isNone && costClear.executed==expectedClear &&
    workerClean final && retained && final.regs.all (fun v => !v) do
    throw <| IO.userError "Original serializer cleanup or output preservation failed"
  let allSteps := costIn.executed+costCore.executed+costOut.executed+costClear.executed
  IO.println s!"SERIALIZER_FOUR_ORIGINAL_STAGES_PASS sourceBitInstructionsWithIndividualHalts={allSteps} peakBitsAfterSearch={max costIn.peakTotalBits (max costCore.peakTotalBits (max costOut.peakTotalBits costClear.peakTotalBits))} rowSaved777Bits={(final.words[777]!).length} totalInternalMs={(← IO.monoMsNow)-t0}"
  (← IO.getStdout).flush
  return final

end IndependentNativeParameters.Serializer
