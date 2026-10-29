import NativeParametersPhysical
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

/-! Genuine OAI graph-code search bit instructions on original 40x896 leaf.
Inputs are fully computed by the earlier source-derived canonical/parameter
stages. This code NEVER writes expected graph results into the input. -/
namespace IndependentNativeParameters.Graph
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeParameters.Physical

set_option maxRecDepth 22000

abbrev GraphCmd := SparseCodeSearch.graphSearch
abbrev GraphLabels : Nat := StructuredCalls.size GraphCmd + 1

def src : Array (Instr 16 48 GraphLabels) :=
  IndependentNonterminal.Linearize.instructionArray GraphCmd

def physical : Array (Instr 40 896 GraphLabels) :=
  src.map (fun op => ProgramLinking.relocateInstr
    NativeCode.registers NativeCode.stackMap id none op)

def localView (x : Bank) (e : Fin GraphLabels) : CompactState GraphLabels :=
  ⟨some e, Array.ofFn (fun i : Fin 16 => x.regs[i.val]!),
   Array.ofFn (fun i : Fin 48 => x.words[i.val]!)⟩

def matchPhysical (x : Bank) (localResult : CompactState GraphLabels) : Bool :=
  localResult.registers == Array.ofFn (fun i : Fin 16 => x.regs[i.val]!) &&
  localResult.words == Array.ofFn (fun i : Fin 48 => x.words[i.val]!)

def runGraph (fuel : Nat) : IO Unit := do
  let began ← IO.monoMsNow
  let saved ← runFive fuel
  IO.println s!"GRAPH_PARAMETERS_REAL ready={metadataCorrect 1 8 saved} dataBits={bits saved} D_unary={(saved.words[808]!).length} r_unary={(saved.words[812]!).length} binaryDegree={BinaryArithmetic.toNat (saved.words[801]!)}"
  (← IO.getStdout).flush
  let inputCmd := routes NativeCode.graphInputs
  let routeOps := IndependentNonterminal.Linearize.instructionArray inputCmd
  let routeEntry : Fin (StructuredCalls.size inputCmd + 1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry inputCmd 1 0)
  let (inputC,rst) := runInstrumented routeOps (inject saved routeEntry) fuel
  IO.println s!"GRAPH_INPUT_ROUTING halted={inputC.pc.isNone} steps={rst.executed} sourceLabels={routeOps.size} D_word={(inputC.words[30]!).length} r_word={(inputC.words[33]!).length} rD_word={(inputC.words[46]!).length}"
  (← IO.getStdout).flush
  unless inputC.pc.isNone do throw <| IO.userError "Graph original input route did not halt"
  let entry : Fin GraphLabels := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry GraphCmd 1 0)
  let table := physical
  IO.println s!"GRAPH_ORIGINAL_SOURCE_PROGRAM staticLabels={table.size} expectedLabels={GraphLabels} sourceEntry={entry.val} fuel={fuel}"
  (← IO.getStdout).flush
  unless table.size == GraphLabels do throw <| IO.userError "Graph code table incorrect size"
  let started ← IO.monoMsNow
  let (endState,st) := runInstrumented table (inject (bank inputC) entry) fuel
  let stopped ← IO.monoMsNow
  IO.println s!"GRAPH_ORIGINAL_SEARCH_RESULT halted={endState.pc.isNone} executedSteps={st.executed} occupiedStackPeak={st.peakTotalBits} longestStack={st.peakSingleBits} visitedPC={st.visitedDistinctLabels} selectedMatrixWordBits={(endState.words[29]!).length} bitInstructionsMs={stopped-started}"
  (← IO.getStdout).flush
  unless endState.pc.isNone do throw <| IO.userError "Actual graph code search did not halt under the fuel cap"
  let (reference,refStats) := runInstrumented src (localView (bank inputC) entry) fuel
  let matched := reference.pc == endState.pc &&
    matchPhysical (bank endState) reference && refStats.executed==st.executed
  IO.println s!"GRAPH_ORIGINAL_SEARCH_AUDIT allSource16x48StateEqual={matched} executedSourceSteps={st.executed} savedCandidateLength={(endState.words[29]!).length} internalTotalMs={(← IO.monoMsNow)-began}"
  (← IO.getStdout).flush
  unless matched do throw <| IO.userError "Graph code search deviates from original 16x48 core"

end IndependentNativeParameters.Graph
