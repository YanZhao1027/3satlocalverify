import CompactNative40
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgramFinal

/-! The next ORIGINAL paper program: physical HashParametersProgram.ABI.command,
with its real input moves, 8x22 inner original arithmetic, output moves and
working-stack cleanup. Inputs are ONLY n=3, m=1, B=8; all other data blank.
No SAT count, expected answer, or precomputed source table is injected. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 19000
set_option maxHeartbeats 1200000

def originalABI : StructuredCalls.Cmd 16 44 := HashParametersProgram.ABI.command

def actualABIInput : StructuredCalls.State 16 44 :=
  ⟨fun _ => false, fun i =>
    if i = (14 : Fin 44) then (3 : Nat).bits
    else if i = 15 then (1 : Nat).bits
    else if i = 16 then (8 : Nat).bits
    else []⟩

/-- First step up the physical paper hierarchy: from 8×22 kernel arithmetic
to 16×44 complete ABI dispatch including cleanup. -/
def measureABI (fuel : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let sites := StructuredCalls.size originalABI
  IO.println s!"ABI_PREPARE staticSites={sites} fuel={fuel} n=3 m=1 B=8"
  let table : Array (Instr 16 44 (StructuredCalls.size originalABI + 1)) :=
    IndependentNonterminal.Linearize.instructionArray originalABI
  let entryNum := IndependentNonterminal.Linearize.callEntry originalABI 1 0
  let entry : Fin (StructuredCalls.size originalABI + 1) := Fin.ofNat _ entryNum
  let t1 ← IO.monoMsNow
  IO.println s!"ABI_TABLE size={table.size} entry={entryNum} build_ms={t1-t0}"
  let (endState, st) := runInstrumented table
    (copyConfig (actualABIInput.withPC (some entry))) fuel
  let t2 ← IO.monoMsNow
  let actualFinal := endState.words.foldl (fun a w => a+w.length) 0
  IO.println s!"ABI_RUNTIME halted={endState.pc.isNone} steps={st.executed} peakStackBits={st.peakTotalBits} peakSingleBits={st.peakSingleBits} finalBits={st.finalTotalBits} recheckedFinalBits={actualFinal} distinctSites={st.visitedDistinctLabels} sets={st.set} copies={st.copy} logic={st.bitLogic} branches={st.tests} pushes={st.push} pops={st.pop} peeks={st.peek} gotos={st.goto} halts={st.halt} run_ms={t2-t1}"
  IO.println s!"ABI_OUTPUT alpha={(BinaryArithmetic.toNat (endState.words[0]!))} depthDenom={(BinaryArithmetic.toNat (endState.words[5]!))} rounds={(BinaryArithmetic.toNat (endState.words[6]!))} inputN={(BinaryArithmetic.toNat (endState.words[14]!))} inputM={(BinaryArithmetic.toNat (endState.words[15]!))} inputB={(BinaryArithmetic.toNat (endState.words[16]!))}"
  unless st.finalTotalBits==actualFinal &&
    st.executed==st.set+st.copy+st.bitLogic+st.tests+st.push+st.pop+st.peek+st.goto+st.halt do
      throw <| IO.userError "ABI bit or opcode accounting mismatch"
  unless endState.pc.isNone &&
    BinaryArithmetic.toNat (endState.words[0]!)==3 &&
    BinaryArithmetic.toNat (endState.words[5]!)==1280000 &&
    BinaryArithmetic.toNat (endState.words[6]!)==10 do
      throw <| IO.userError "ABI output incorrect or fuel exhausted"

end IndependentNativeCost
