import NativeStartStages

/-! Single-PC monolithic 3036-label source-bit simulation of the ORIGINAL
LeafOuterProgram.start instruction tree, linking its original four source
command tables: ClauseCount caller, hash ABI mapped to 40x896, cleanup Wide
mapped to lower 768 physical stacks, saveWidth route. The ORIGINAL opcode
constructors are used unchanged; label relocations are explicit and charged.

The linking transform is an independent compiler; its full equivalence to the
upstream `StructuredCalls.compiled start` remains a distinct audit task.
-/
namespace IndependentNativeStart.Linked
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open IndependentNativeCost
open IndependentNativeCost.PhysicalStream
open IndependentNativeStart

set_option maxRecDepth 25000
set_option maxHeartbeats 1500000

abbrev Total : Nat := 3036
abbrev Clause : Nat := 40
abbrev Hash : Nat := 637
abbrev Cleanup : Nat := 2348
abbrev Save : Nat := 12

def cl : Array (Instr 40 896 Clause) :=
  IndependentNonterminal.Linearize.instructionArray LeafProgram.ClauseCount.caller

def hash : Array (Instr 16 44 Hash) :=
  IndependentNonterminal.Linearize.instructionArray HashParametersProgram.ABI.command

def cleanup : Array (Instr 40 768 Cleanup) :=
  IndependentNonterminal.FastLinearize.instructionArray LeafProgram.Cleanup.Wide.command

def save : Array (Instr 40 896 Save) :=
  IndependentNonterminal.FastLinearize.instructionArray LeafOuterProgram.saveWidth

def clauseBase : Nat := 0
def hashBase : Nat := Clause
def cleanupBase : Nat := hashBase + Hash
def saveBase : Nat := cleanupBase + Cleanup - 1

def clEntry : Nat := IndependentNonterminal.Linearize.callEntry LeafProgram.ClauseCount.caller 1 0

def hashEntry : Nat := IndependentNonterminal.Linearize.callEntry HashParametersProgram.ABI.command 1 0

def cleanupEntry : Nat := IndependentNonterminal.Linearize.callEntry LeafProgram.Cleanup.Wide.command 1 0

def saveEntry : Nat := IndependentNonterminal.Linearize.callEntry LeafOuterProgram.saveWidth 1 0

private def place (n : Nat) : Fin Total := Fin.ofNat _ n
private def mapHashR (i : Fin 16) : Fin 40 := Fin.ofNat _ (PhysicalPort.register i)
private def mapHashS (i : Fin 44) : Fin 896 := Fin.ofNat _ (PhysicalPort.stack i)
private def mapWorkS (i : Fin 768) : Fin 896 := Fin.ofNat _ i.val

/-- 0 is the source program's old HALT label. A call site embeds that HALT as
its return branch to the following command. The other labels are relocated
by a constant offset. For top-level `.seq` commands, the old label 0 is not
stored, but all jumps to 0 target the next command's entry. -/
def pack {r s n : Nat} (source : Array (Instr r s n)) (base exit : Nat)
    (reg : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (omitHalt : Bool) : Array (Instr 40 896 Total) := Id.run do
  let mut result := #[]
  for i in [:source.size] do
    if !omitHalt || i != 0 then
      let original : Instr r s n := (source[i]?).getD .halt
      let embedded := ProgramLinking.relocateInstr reg stack
        (fun pc : Fin n => place (if pc.val == 0 then (if omitHalt then exit else base) else base+pc.val))
        (some (place exit)) original
      result := result.push embedded
  return result

def linked : Array (Instr 40 896 Total) := Id.run do
  let mut result : Array (Instr 40 896 Total) := #[Instr.halt]
  result := result ++ pack cl clauseBase (hashBase + hashEntry) id id true
  result := result ++ pack hash hashBase (cleanupBase + cleanupEntry) mapHashR mapHashS false
  result := result ++ pack cleanup cleanupBase (saveBase+saveEntry) id mapWorkS false
  result := result ++ pack save saveBase 0 id id true
  return result

/-- Verify full one-label sequence and output against the independent stage
reference (same original source subprograms, separately compiled). -/
def runLinked (fuel : Nat) : IO Unit := do
  let startTime ← IO.monoMsNow
  IO.println s!"LINKED_START_PREP expectedOriginalSites={Total-1} clauseLabels={Clause} hashLabels={Hash} cleanupLabels={Cleanup} saveLabels={Save} expectedAllLabels={Total} baseHash={hashBase} baseCleanup={cleanupBase} baseSave={saveBase} initialEntry={clEntry} originalEntryPrechecked=3"
  (← IO.getStdout).flush
  let physical := linked
  let compiledMs ← IO.monoMsNow
  IO.println s!"LINKED_START_CODE actualLabels={physical.size} expectedLabels={Total} compiledMs={compiledMs-startTime}"
  (← IO.getStdout).flush
  unless physical.size == Total && Total == 3036 &&
    hashBase==40 && cleanupBase==677 && saveBase==3024 &&
    clEntry == 3 do
    throw <| IO.userError "Full original source code positions do not match staged compiler"
  let input := copyConfig (loadedLocalInput.withPC (some (place clEntry)))
  let (final,metrics) := runInstrumented physical input fuel
  let finishedMs ← IO.monoMsNow
  IO.println s!"LINKED_START_EXEC halted={final.pc.isNone} steps={metrics.executed} peakTotalStackBits={metrics.peakTotalBits} peakSingleStackBits={metrics.peakSingleBits} initialBits={metrics.initialBits} finalBits={metrics.finalTotalBits} recountedFinal={occupied (takeFrame final)} visitedSites={metrics.visitedDistinctLabels} instructionMs={finishedMs-compiledMs}"
  IO.println s!"LINKED_START_OUTPUT formulaCount={BinaryArithmetic.toNat (final.words[782]!)} alphabet={BinaryArithmetic.toNat (final.words[768]!)} distanceDenom={BinaryArithmetic.toNat (final.words[773]!)} loopCap={BinaryArithmetic.toNat (final.words[774]!)} savedWidth={BinaryArithmetic.toNat (final.words[783]!)} workerClean={workerEmpty (takeFrame final)} allRegsBlank={allRegsClear (takeFrame final)}"
  (← IO.getStdout).flush
  unless final.pc.isNone && metrics.executed == 6135 &&
    metrics.peakTotalBits == 125 && metrics.finalTotalBits == 53 &&
    occupied (takeFrame final) == metrics.finalTotalBits &&
    workerEmpty (takeFrame final) && allRegsClear (takeFrame final) &&
    BinaryArithmetic.toNat (final.words[768]!) == 3 &&
    BinaryArithmetic.toNat (final.words[783]!) == 3 &&
    BinaryArithmetic.toNat (final.words[773]!) == 1280000 &&
    BinaryArithmetic.toNat (final.words[774]!) == 10 do
    throw <| IO.userError "Single program source trace did not match expected complete source prep"
  IO.println "LINKED_START_SINGLE_PROGRAM_PASS original four-stage source opcodes, one PC, one final HALT"

end IndependentNativeStart.Linked
