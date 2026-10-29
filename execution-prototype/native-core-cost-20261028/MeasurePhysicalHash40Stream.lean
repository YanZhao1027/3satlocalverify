import CompactNative40
import PhysicalPortMapProof
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHashParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgramFinal

/-! Execute original 16x44 ABI instructions on the ACTUAL 40x896 leaf-bank
storage, using original ProgramLinking.relocateInstr at EACH executed step.
This preserves exact upstream registers/stack mapping without materializing the
expensive dependent 40x896 typed instruction table. Call/return overhead is
accounted separately. No #SAT counting or oracle is supplied. -/

namespace IndependentNativeCost.PhysicalStream
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog

set_option maxRecDepth 18000
set_option maxHeartbeats 1000000

abbrev Cmd := HashParametersProgram.ABI.command
abbrev L : Nat := StructuredCalls.size Cmd + 1

def sourceTable : Array (Instr 16 44 L) :=
  IndependentNonterminal.Linearize.instructionArray Cmd

def sourceEntry : Fin L :=
  Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry Cmd 1 0)

/-- Exact original physical register and stack relocation for each opcode. -/
def liftSource (op : Instr 16 44 L) : Instr 40 896 L :=
  ProgramLinking.relocateInstr
    LeafProgram.HashParameters.registers
    LeafProgram.HashParameters.stackMap
    id none op

/-- Run genuine lifted bit instructions on 40 physical registers, 896 stacks.
The current PC is the INNER source PC before global caller shift. -/
def runPhysicalSource (table : Array (Instr 16 44 L))
    (start : CompactState L) (fuel : Nat) : CompactState L × Counters := Id.run do
  let mut c := start
  let mut st := statsInitial c
  let mut labels : Std.HashSet Nat := {}
  for _ in [:fuel] do
    let some pc := c.pc | break
    let some original := table[pc.val]? | break
    labels := labels.insert pc.val
    let op := liftSource original
    let before := c
    c := runOne op c
    st := {st with executed := st.executed + 1}
    match op with
    | .halt => st := {st with halt := st.halt + 1}
    | .goto _ => st := {st with goto := st.goto + 1}
    | .set _ _ _ => st := {st with set := st.set + 1}
    | .copy _ _ _ => st := {st with copy := st.copy + 1}
    | .bnot _ _ _ | .band _ _ _ _ | .bor _ _ _ _ | .bxor _ _ _ _ =>
        st := {st with bitLogic := st.bitLogic + 1}
    | .branch _ _ _ => st := {st with tests := st.tests + 1}
    | .push port _ _ =>
        st := {st with push := st.push + 1, finalTotalBits := st.finalTotalBits + 1, peakSingleBits := max st.peakSingleBits ((before.words[port.val]!).length + 1)}
    | .pop port _ _ _ =>
        st := {st with pop := st.pop + 1, finalTotalBits := st.finalTotalBits - (if (before.words[port.val]!).isEmpty then 0 else 1)}
    | .peek _ _ _ _ => st := {st with peek := st.peek + 1}
    st := {st with peakTotalBits := max st.peakTotalBits st.finalTotalBits}
  return (c, {st with visitedDistinctLabels := labels.size})

def project (registers : Array Bool) (words : Array (List Bool)) : CompactState L :=
  {pc := none,
   registers := Array.ofFn (fun i : Fin 16 =>
     registers[PhysicalPort.register i]!),
   words := Array.ofFn (fun i : Fin 44 =>
     words[PhysicalPort.stack i]!)}

def allUnmappedPreserved (regsA regsB : Array Bool)
    (wordsA wordsB : Array (List Bool)) : Bool := Id.run do
  let mappedRegs : Std.HashSet Nat :=
    (List.finRange 16).foldl
      (fun x i => x.insert (PhysicalPort.register i)) {}
  let mappedWords : Std.HashSet Nat :=
    (List.finRange 44).foldl
      (fun x i => x.insert (PhysicalPort.stack i)) {}
  for i in [:40] do
    if !mappedRegs.contains i && regsA[i]! != regsB[i]! then return false
  for i in [:896] do
    if !mappedWords.contains i && wordsA[i]! != wordsB[i]! then return false
  return true

def recount (words : Array (List Bool)) : Nat :=
  words.foldl (fun s w => s + w.length) 0

/-- Independent every-step cost check on physical 40x896 (small workload).
Can be switched on to cross-check peak occupied bits against the delta
accounting; this does not itself establish interpreter correctness. -/
def checkPhysicalEveryStep (table : Array (Instr 16 44 L))
    (start : CompactState L) (fuel : Nat) : Bool := Id.run do
  let mut c := start
  let mut peak := recount c.words
  let mut maxSingle := c.words.foldl (fun acc w => max acc w.length) 0
  let mut count := 0
  for _ in [:fuel] do
    let some pc := c.pc | break
    let some original := table[pc.val]? | return false
    c := runOne (liftSource original) c
    count := count + 1
    peak := max peak (recount c.words)
    maxSingle := max maxSingle (c.words.foldl (fun acc w => max acc w.length) 0)
  let (fast,st) := runPhysicalSource table start fuel
  return fast.pc == c.pc && fast.registers == c.registers && fast.words == c.words &&
    count == st.executed && peak == st.peakTotalBits &&
    maxSingle == st.peakSingleBits && recount c.words == st.finalTotalBits

/-- First a real physical nonempty formula -> original ClauseCount.caller;
then original HashParametersProgram.ABI.command with actual registers/stack
mapping used by original LeafProgram.HashParameters.command. -/
def measure (fuel : Nat) (checkEveryStep : Bool) : IO Unit := do
  let begin ← IO.monoMsNow
  let clauseCmd := LeafProgram.ClauseCount.caller
  let clauseTable : Array (Instr 40 896 (StructuredCalls.size clauseCmd + 1)) :=
    IndependentNonterminal.Linearize.instructionArray clauseCmd
  let clauseEntry : Fin (StructuredCalls.size clauseCmd+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry clauseCmd 1 0)
  let (clauseEnd,clauseCost) := runInstrumented clauseTable
    (copyConfig (loadedLocalInput.withPC (some clauseEntry))) fuel
  IO.println s!"REAL_PHYSICAL_CLAUSE halted={clauseEnd.pc.isNone} steps={clauseCost.executed} count={BinaryArithmetic.toNat (clauseEnd.words[782]!)} peakDataBits={clauseCost.peakTotalBits}"
  (← IO.getStdout).flush
  unless clauseEnd.pc.isNone && clauseCost.executed == 180 &&
    BinaryArithmetic.toNat (clauseEnd.words[782]!) == 1 do
    throw <| IO.userError "Original clause counter failed"
  let tableStart ← IO.monoMsNow
  let table : Array (Instr 16 44 L) :=
    IndependentNonterminal.Linearize.instructionArray Cmd
  IO.println s!"ORIGINAL_ABI_SOURCE_TABLE size={table.size} expected={L} materialize_ms={(← IO.monoMsNow)-tableStart}"
  (← IO.getStdout).flush
  unless table.size == L do throw <| IO.userError "Incorrect ABI source table size"
  let input : CompactState L :=
    {pc := some sourceEntry, registers := clauseEnd.registers, words := clauseEnd.words}
  let startExec ← IO.monoMsNow
  let (done,st) := runPhysicalSource table input fuel
  let ended ← IO.monoMsNow
  IO.println s!"REAL_PHYSICAL_HASH halted={done.pc.isNone} stepsABI={st.executed} stepsWithOuterHalt={st.executed+1} peakTotalStackBits={st.peakTotalBits} peakSingleStackBits={st.peakSingleBits} initialDataBits={st.initialBits} finalDataBits={st.finalTotalBits} recountedFinalBits={recount done.words} sourceLabelsVisited={st.visitedDistinctLabels} instruction_ms={ended-startExec}"
  (← IO.getStdout).flush
  IO.println s!"REAL_PHYSICAL_OUTPUT m={BinaryArithmetic.toNat (done.words[782]!)} alpha={BinaryArithmetic.toNat (done.words[768]!)} distanceDenom={BinaryArithmetic.toNat (done.words[773]!)} loopCap={BinaryArithmetic.toNat (done.words[774]!)} n={BinaryArithmetic.toNat (done.words[785]!)} B={BinaryArithmetic.toNat (done.words[786]!)}"
  (← IO.getStdout).flush
  let sourceStart : CompactState L := {(project clauseEnd.registers clauseEnd.words) with pc := some sourceEntry}
  let (sourceEnd,sourceCost) := runInstrumented table sourceStart fuel
  let projectedEnd := project done.registers done.words
  let sourceMatch := done.pc == sourceEnd.pc &&
    projectedEnd.registers == sourceEnd.registers &&
    projectedEnd.words == sourceEnd.words && st.executed == sourceCost.executed
  let frameMatch := allUnmappedPreserved clauseEnd.registers done.registers clauseEnd.words done.words
  IO.println s!"REAL_PHYSICAL_AUDIT ABI_steps={sourceCost.executed} ABI_original_state_match={sourceMatch} unmapped40x896_frame_preserved={frameMatch} raw_total_steps={clauseCost.executed+st.executed+1}"
  (← IO.getStdout).flush
  if checkEveryStep then
    let recomputed := checkPhysicalEveryStep table input fuel
    IO.println s!"REAL_PHYSICAL_EVERY_STEP_SPACE_CHECK equal={recomputed}"
    (← IO.getStdout).flush
    unless recomputed do throw <| IO.userError "Physical stack-space mismatch"
  IO.println s!"REAL_PHYSICAL_RUN wall_internal_ms={ended-begin}"
  (← IO.getStdout).flush
  unless done.pc.isNone && st.executed==3585 && sourceMatch && frameMatch &&
      st.finalTotalBits == recount done.words &&
      BinaryArithmetic.toNat (done.words[768]!)==3 &&
      BinaryArithmetic.toNat (done.words[773]!)==1280000 &&
      BinaryArithmetic.toNat (done.words[774]!)==10 do
    throw <| IO.userError "Actual mapped original hash command did not finish or disagreed"

end IndependentNativeCost.PhysicalStream
