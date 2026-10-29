import NativeGraphSearchPhysical

/-! Genuine graph AND local source searches, from earlier physical metadata,
including original graph inputs / search / graph output route / lower-bank
cleanup and then original local inputs / search / local output / cleanup.
No SAT answer or code matrix is preloaded. Tests 16x48 source vs mapped 40x896
physical machine for BOTH search cores; this is staged, not a single `searches`
monolithic code table or a verified Good/Distance certificate yet. -/
namespace IndependentNativeParameters.TwoSearches
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeParameters.Physical

set_option maxRecDepth 23000

/-- Original routed physical operations, no substitute copy/clear logic. -/
def runCmd (name : String) (cmd : StructuredCalls.Cmd 40 896)
    (start : Bank) (fuel : Nat) : IO (Bank × Nat × Nat) := do
  let code := IndependentNonterminal.Linearize.instructionArray cmd
  let entry : Fin (StructuredCalls.size cmd+1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry cmd 1 0)
  let (done,cost) := runInstrumented code (inject start entry) fuel
  IO.println s!"TWO_SEARCH_ROUTE name={name} halted={done.pc.isNone} steps={cost.executed} labels={code.size} peakBits={cost.peakTotalBits}"
  (← IO.getStdout).flush
  unless done.pc.isNone do throw <| IO.userError s!"Original {name} operation did not halt"
  return (bank done,cost.executed,cost.peakTotalBits)

abbrev Graph := SparseCodeSearch.graphSearch
abbrev Local := SparseCodeSearch.localSearch

def runCore (name : String) (cmd : StructuredCalls.Cmd 16 48)
    (beginBank : Bank) (fuel : Nat) : IO (Bank × Nat × Nat) := do
  let source := IndependentNonterminal.Linearize.instructionArray cmd
  let mapped := source.map (fun op => ProgramLinking.relocateInstr
    NativeCode.registers NativeCode.stackMap id none op)
  let entry : Fin (StructuredCalls.size cmd + 1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry cmd 1 0)
  let beginCfg := inject beginBank entry
  let (out,stat) := runInstrumented mapped beginCfg fuel
  IO.println s!"TWO_SEARCH_CORE name={name} halted={out.pc.isNone} steps={stat.executed} sourceLabels={source.size} mappedLabels={mapped.size} peakBits={stat.peakTotalBits} maxSingle={stat.peakSingleBits} selectedWord29={(out.words[29]!).length} selectedWord18={(out.words[18]!).length}"
  (← IO.getStdout).flush
  unless out.pc.isNone do throw <| IO.userError s!"Original source {name} search exhausted fuel"
  let localInput : CompactState (StructuredCalls.size cmd+1) :=
    ⟨some entry, Array.ofFn (fun i : Fin 16 => beginBank.regs[i.val]!),
     Array.ofFn (fun i : Fin 48 => beginBank.words[i.val]!)⟩
  let (reference,refSteps) := runInstrumented source localInput fuel
  let physical := bank out
  let agree := reference.pc==out.pc && stat.executed==refSteps.executed &&
    reference.registers==Array.ofFn (fun i : Fin 16 => physical.regs[i.val]!) &&
    reference.words==Array.ofFn (fun i : Fin 48 => physical.words[i.val]!)
  IO.println s!"TWO_SEARCH_SOURCE_MAPPING_AUDIT name={name} all16RegistersAnd48StacksEqual={agree} executedSteps={stat.executed}"
  (← IO.getStdout).flush
  unless agree do throw <| IO.userError s!"Source-vs-physical search diverged: {name}"
  return (physical,stat.executed,stat.peakTotalBits)

def run (fuel : Nat) : IO Bank := do
  let begin ← IO.monoMsNow
  let ready ← runFive fuel
  IO.println s!"TWO_SEARCH_START actualParametersReady={metadataCorrect 1 8 ready} sourcePeakDataBits=252"
  (← IO.getStdout).flush
  let (g1,sg1,pg1) ← runCmd "graph_input" (routes NativeCode.graphInputs) ready fuel
  let (g2,sg2,pg2) ← runCore "graph_search" Graph g1 fuel
  let (g3,sg3,pg3) ← runCmd "graph_save" (route (29,816)) g2 fuel
  let (g4,sg4,pg4) ← runCmd "graph_clear48" NativeCode.clearLower g3 fuel
  IO.println s!"TWO_SEARCH_GRAPH_COMPLETE candidateSaved816Bits={(g4.words[816]!).length} all48WorkStacksClean={(List.range 48).all (fun i => (g4.words[i]!).isEmpty)} copiedCandidateCorrect={g4.words[816]! == g2.words[29]!}"
  (← IO.getStdout).flush
  unless (List.range 48).all (fun i => (g4.words[i]!).isEmpty) &&
    g4.words[816]! == g2.words[29]! do
    throw <| IO.userError "Original graph candidate save and worker clear failed"
  let (l1,sl1,pl1) ← runCmd "local_input" (routes NativeCode.localInputs) g4 fuel
  let (l2,sl2,pl2) ← runCore "local_search" Local l1 fuel
  let (l3,sl3,pl3) ← runCmd "local_save" (route (18,815)) l2 fuel
  let (l4,sl4,pl4) ← runCmd "local_clear48" NativeCode.clearLower l3 fuel
  let both := l4.words[816]! == g4.words[816]! && l4.words[815]! == l2.words[18]!
  let clear := (List.range 48).all (fun i => (l4.words[i]!).isEmpty)
  let twoSteps := sg1+sg2+sg3+sg4+sl1+sl2+sl3+sl4
  let peak := [252,pg1,pg2,pg3,pg4,pl1,pl2,pl3,pl4].foldl max 0
  IO.println s!"TWO_SEARCH_BOTH_COMPLETE candidateGraph816Bits={(l4.words[816]!).length} candidateLocal815Bits={(l4.words[815]!).length} bothCandidatesPersisted={both} all48WorkStacksClean={clear} bothSourceSearchSteps={sg2+sl2} allEightSubstagesStepsIncludingHalts={twoSteps} peakDataBitsFromParametersToBothSearches={peak} totalWallInternalMs={(← IO.monoMsNow)-begin}"
  (← IO.getStdout).flush
  unless both && clear do throw <| IO.userError "Original two code searches did not persist candidates"
  return l4

end IndependentNativeParameters.TwoSearches
