import NativeFinishChunked

/-! Run EXACT upstream StructuredCalls.compiled afterCode source opcodes,
independently check every label against fast linearizer, and count all
primitive boolean instructions. Runtime executions are bounded prefixes;
the original #SAT solver is not replaced or claimed complete. -/
namespace NativeFinishOriginalDirect

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open IndependentNativeCost
open IndependentNativeParameters.Physical

set_option maxRecDepth 26000
set_option maxHeartbeats 3000000

def cmd := NativeLeafPreparation.afterCode
abbrev Total : Nat := StructuredCalls.size cmd + 1
def source := StructuredCalls.compiled cmd 784 788
def originalCode : Array (Instr 40 896 Total) :=
  ((List.finRange Total).map (fun pc => source.code pc)).toArray

def fastCode : Array (Instr 40 896 Total) :=
  IndependentNonterminal.FastLinearize.instructionArray cmd

def run (chunkSize chunks : Nat) : IO Unit := do
  let begin <- IO.monoMsNow
  let orig := originalCode
  let fast := fastCode
  let entry := source.entry
  IO.println s!"DIRECT_ORIGINAL_COMPILER sourceLabels={Total} originalTableSize={orig.size} independentTableSize={fast.size} originalEntry={entry.val}"
  (← IO.getStdout).flush
  unless orig.size == Total && fast.size == Total do
    throw <| IO.userError "wrong source instruction table dimensions"
  for pc in [:Total] do
    unless (orig[pc]?).getD Instr.halt == (fast[pc]?).getD Instr.halt do
      throw <| IO.userError s!"original opcode mismatched local linearizer at {pc}"
  IO.println s!"DIRECT_ORIGINAL_ALL_OPCODES_MATCH labels={Total}"
  (← IO.getStdout).flush
  let ready <- IndependentNativeParameters.Serializer.runSerializer 180000
  let originalData : LeafOuterProgram.Data :=
    ⟨fun i => ready.regs[i.val]!, fun i => ready.words[i.val]!⟩
  let expected := HashGreedyProgram.Initialize.zeroWord originalData
  let originalRows := ready.words[777]!
  IO.println s!"DIRECT_ORIGINAL_INPUT sourceRowBits={originalRows.length} theoreticalZeroWordBits={expected.length} initialDataBits={bits ready}"
  (← IO.getStdout).flush
  let mut current := inject ready entry
  let mut count := 0
  let mut peak := bits ready
  let mut maxSingle := 0
  let mut pushes := 0
  let mut pops := 0
  let mut peeks := 0
  let mut branches := 0
  let mut gotos := 0
  let mut sets := 0
  let mut copies := 0
  let mut bitlogic := 0
  let mut halts := 0
  for k in [:chunks] do
    let t0 <- IO.monoMsNow
    let (next, stats) := runInstrumented orig current chunkSize
    current := next
    count := count + stats.executed
    peak := max peak stats.peakTotalBits
    maxSingle := max maxSingle stats.peakSingleBits
    pushes := pushes + stats.push
    pops := pops + stats.pop
    peeks := peeks + stats.peek
    branches := branches + stats.tests
    gotos := gotos + stats.goto
    sets := sets + stats.set
    copies := copies + stats.copy
    bitlogic := bitlogic + stats.bitLogic
    halts := halts + stats.halt
    let currentBits := (current.words[778]!).length
    IO.println s!"DIRECT_ORIGINAL_PROGRESS chunk={k+1} steps={count} halted={current.pc.isNone} sourcePC={current.pc.map Fin.val} zeroWordBits={currentBits} peakDataBits={peak} longestStack={maxSingle} push={pushes} pop={pops} peek={peeks} branch={branches} goto={gotos} set={sets} copy={copies} bitLogic={bitlogic} halt={halts} chunkMs={(← IO.monoMsNow)-t0}"
    (← IO.getStdout).flush
    unless current.words[777]! == originalRows do
      throw <| IO.userError "unexpected mutation of serialized rows"
    if count == 2000000 then
      unless currentBits == 35238 && peak == 35368 do
        throw <| IO.userError "historical 2M step reference mismatch"
    if count == 4000000 then
      unless currentBits == 70478 && peak == 70608 do
        throw <| IO.userError "historical 4M step reference mismatch"
    if current.pc.isNone then break
  IO.println s!"DIRECT_ORIGINAL_RESULT steps={count} halted={current.pc.isNone} currentBits={(current.words[778]!).length} targetBits={expected.length} maxDataBits={peak} rowsPreserved={current.words[777]! == originalRows} allOpcodesMatch=true sourceFromUpstream=true runMs={(← IO.monoMsNow)-begin}"
  (← IO.getStdout).flush
  if current.pc.isNone && current.words[778]! != expected then
    throw <| IO.userError "halted original source with wrong zero word"
end NativeFinishOriginalDirect
