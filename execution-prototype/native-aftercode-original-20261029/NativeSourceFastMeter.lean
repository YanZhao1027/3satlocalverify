import NativeDirectTraceProof
import NativeFinishOriginalDirect

/-! Alternate host-side O(1)-per-step accounting for every ORIGINAL opcode.
No fast-forward, oracle, answer injection or skipped operation.
The cached 896 stack lengths are recounted at every chunk boundary.
Full-state/full-counters baseline is checked independently. -/

namespace IndependentNativeFastMeter
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open IndependentNativeCost
open IndependentNativeParameters.Physical

/-- Construct the exact upstream finishedWords once, sharing the large
zero candidate across all 896 ports instead of recomputing it 896 times. -/
def cachedExpectedWords (a : LeafOuterProgram.Data) : Array (List Bool) :=
  let zeroCandidate := HashGreedyProgram.Initialize.zeroWord a
  let base : Array (List Bool) := Array.ofFn (HashGreedyProgram.Initialize.finishedStacks a)
  (base.set! 778 zeroCandidate).set! 779 []

/-- Kernel-checked cached expected store equals the upstream reference,
not merely sample output length. -/
theorem cachedExpectedWords_correct (a : LeafOuterProgram.Data) :
    cachedExpectedWords a = Array.ofFn (NativeLeafPreparation.finishedWords a) := by
  simp [cachedExpectedWords, NativeLeafPreparation.finishedWords,
    IndependentNativeCompactProof.ofFn_update]

def source := NativeFinishOriginalDirect.source
def table := NativeFinishOriginalDirect.originalCode

def runMeter {r s l : Nat} (code : Array (Instr r s l))
    (input : CompactState l) (fuel : Nat) :
    CompactState l × Counters × Array Nat := Id.run do
  let mut current := input
  let mut counts := statsInitial input
  let mut lengths := input.words.map List.length
  let mut visited : Std.HashSet Nat := {}
  for _ in [:fuel] do
    let some pc := current.pc | break
    let some op := code[pc.val]? | break
    visited := visited.insert pc.val
    match op with
    | .push stack _ _ =>
        let prev := lengths[stack.val]!
        lengths := lengths.set! stack.val (prev + 1)
        counts := {counts with
          push := counts.push + 1,
          finalTotalBits := counts.finalTotalBits + 1,
          peakSingleBits := max counts.peakSingleBits (prev+1)}
    | .pop stack _ _ _ =>
        let prev := lengths[stack.val]!
        let removed := if prev == 0 then 0 else 1
        lengths := lengths.set! stack.val (prev - removed)
        counts := {counts with
          pop := counts.pop + 1,
          finalTotalBits := counts.finalTotalBits - removed}
    | .peek _ _ _ _ => counts := {counts with peek := counts.peek + 1}
    | .branch _ _ _ => counts := {counts with tests := counts.tests + 1}
    | .goto _ => counts := {counts with goto := counts.goto + 1}
    | .set _ _ _ => counts := {counts with set := counts.set + 1}
    | .copy _ _ _ => counts := {counts with copy := counts.copy + 1}
    | .bnot _ _ _ | .band _ _ _ _ | .bor _ _ _ _ | .bxor _ _ _ _ =>
        counts := {counts with bitLogic := counts.bitLogic + 1}
    | .halt => counts := {counts with halt := counts.halt + 1}
    current := runOne op current
    counts := {counts with
      executed := counts.executed + 1,
      peakTotalBits := max counts.peakTotalBits counts.finalTotalBits}
  counts := {counts with visitedDistinctLabels := visited.size}
  return (current, counts, lengths)

def opcodeTotal (c : Counters) : Nat :=
  c.push+c.pop+c.peek+c.tests+c.goto+c.set+c.copy+c.bitLogic+c.halt

def metadataEqual (a b : Counters) : Bool :=
  a.executed == b.executed &&
  a.push == b.push && a.pop == b.pop && a.peek == b.peek &&
  a.tests == b.tests && a.goto == b.goto && a.set == b.set &&
  a.copy == b.copy && a.bitLogic == b.bitLogic && a.halt == b.halt &&
  a.initialBits == b.initialBits && a.peakTotalBits == b.peakTotalBits &&
  a.peakSingleBits == b.peakSingleBits && a.finalTotalBits == b.finalTotalBits &&
  a.visitedDistinctLabels == b.visitedDistinctLabels

def run (chunkSize chunks baselineMillion : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let ops := table
  let original := source
  let full := NativeFinishOriginalDirect.fastCode
  unless ops.size == 119 && ops.size == full.size && original.entry.val == 1 do
    throw <| IO.userError "unexpected original opcode table"
  for i in [:ops.size] do
    unless ops[i]? == full[i]? do
      throw <| IO.userError s!"different upstream opcode at {i}"
  let physical ← IndependentNativeParameters.Serializer.runSerializer 180000
  let oldRows := physical.words[777]!
  let coreData : LeafOuterProgram.Data :=
    ⟨fun i => physical.regs[i.val]!, fun i => physical.words[i.val]!⟩
  let expected := HashGreedyProgram.Initialize.zeroWord coreData
  let first := inject physical original.entry
  let mut current := first
  let mut peak := bits physical
  let mut count := 0
  let mut pushTotal := 0
  let mut popTotal := 0
  let mut peekTotal := 0
  let mut branchTotal := 0
  let mut logicTotal := 0
  let mut gotoTotal := 0
  let mut setTotal := 0
  let mut copyTotal := 0
  let mut haltTotal := 0
  IO.println s!"FAST_METER_START sourceLabels={ops.size} sourceFromOriginal=true initialBits={bits physical} targetBits={expected.length} chunkSize={chunkSize} chunks={chunks} baselineMillion={baselineMillion}"
  (← IO.getStdout).flush
  for chunk in [:chunks] do
    let began ← IO.monoMsNow
    let (next, stats, lens) := runMeter ops current chunkSize
    current := next
    count := count+stats.executed
    peak := max peak stats.peakTotalBits
    pushTotal := pushTotal+stats.push
    popTotal := popTotal+stats.pop
    peekTotal := peekTotal+stats.peek
    branchTotal := branchTotal+stats.tests
    logicTotal := logicTotal+stats.bitLogic
    gotoTotal := gotoTotal+stats.goto
    setTotal := setTotal+stats.set
    copyTotal := copyTotal+stats.copy
    haltTotal := haltTotal+stats.halt
    let actualLengths := current.words.map List.length
    let measuredBits := actualLengths.foldl (·+·) 0
    unless lens == actualLengths && stats.finalTotalBits == measuredBits &&
      stats.executed == opcodeTotal stats && oldRows == current.words[777]! do
      throw <| IO.userError s!"Fast accounting differs from full physical recount chunk={chunk}"
    IO.println s!"FAST_METER_PROGRESS chunk={chunk+1} steps={count} halted={current.pc.isNone} sourcePC={current.pc.map Fin.val} zeroWordBits={(current.words[778]!).length} measuredStackBits={measuredBits} peakDataBits={peak} sourceRowPreserved={oldRows == current.words[777]!} sourceChunkMs={(← IO.monoMsNow)-began}"
    (← IO.getStdout).flush
    if count == 2_000_000 then
      unless (current.words[778]!).length == 35238 && peak == 35368 do
        throw <| IO.userError "Fast meter 2M checkpoint regression"
    if count == 4_000_000 then
      unless (current.words[778]!).length == 70478 && peak == 70608 do
        throw <| IO.userError "Fast meter 4M checkpoint regression"
    if count == 8_000_000 then
      unless (current.words[778]!).length == 140962 && peak == 141092 do
        throw <| IO.userError "Fast meter 8M checkpoint regression"
    if current.pc.isNone then break
  IO.println s!"FAST_METER_RESULT steps={count} halted={current.pc.isNone} zeroWordBits={(current.words[778]!).length} expectedZeroWordBits={expected.length} peakOccupiedDataBits={peak} push={pushTotal} pop={popTotal} peek={peekTotal} branch={branchTotal} bitLogic={logicTotal} goto={gotoTotal} set={setTotal} copy={copyTotal} halt={haltTotal} sourceRowPreserved={oldRows == current.words[777]!} internalMs={(← IO.monoMsNow)-t0}"
  (← IO.getStdout).flush
  if current.pc.isNone && current.words[778]! != expected then
    throw <| IO.userError "Original afterCode halted but has wrong zero candidate"
  if current.pc.isNone then
    let verifiedOriginalWords : Array (List Bool) := cachedExpectedWords coreData
    unless current.words == verifiedOriginalWords do
      throw <| IO.userError "Full original afterCode ended with noncanonical physical stack state"
    IO.println s!"FAST_METER_FINISHED_ORIGINAL_FULL_896_STACKS_PASS expectedZeroWordBits={expected.length} sourceInstructionSteps={count}"
    (← IO.getStdout).flush
  if baselineMillion > 0 then
    let (baseline, baselineStats) := runInstrumented ops first (baselineMillion*1000000)
    let (alternate, fastStats, fastLens) := runMeter ops first (baselineMillion*1000000)
    unless baseline.pc == alternate.pc &&
      baseline.registers == alternate.registers &&
      baseline.words == alternate.words &&
      metadataEqual baselineStats fastStats &&
      fastLens == alternate.words.map List.length do
      throw <| IO.userError "Fast meter fails full-store and full-counters baseline audit"
    IO.println s!"FAST_METER_BASELINE_FULL_STATE_PASS steps={baselineMillion*1000000} all40regsEqual=true all896StacksEqual=true allCountersEqual=true"
    (← IO.getStdout).flush
end IndependentNativeFastMeter

#print axioms IndependentNativeFastMeter.cachedExpectedWords_correct
