import CompactNative40
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgramFinal

/-! MEASUREMENT of the actual original HashParametersProgram.command, whose
Boolean arithmetic constructs the 3m alphabet, sparse distance denominator,
and round cap. This IS part of the real nonterminal query preparation,
although it is not the full query or SAT solver. No oracle values are placed
in the initial state: only n,m,B are supplied. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 19000
set_option maxHeartbeats 1000000

def realArithmeticCommand : StructuredCalls.Cmd 8 22 := HashParametersProgram.command

/-- Three genuine binary scalar input words n=3, m=1, B=8, with scratch blank. -/
def arithmeticInput : StructuredCalls.State 8 22 :=
  SubexpBlockParameterProgram.state (fun _ => false) (HashParametersProgram.inputWords (3 : Nat).bits (1 : Nat).bits (8 : Nat).bits)

def runArithmetic (fuel : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let table : Array (Instr 8 22 (StructuredCalls.size realArithmeticCommand + 1)) :=
    IndependentNonterminal.Linearize.instructionArray realArithmeticCommand
  let entryNum := IndependentNonterminal.Linearize.callEntry realArithmeticCommand 1 0
  let entry : Fin (StructuredCalls.size realArithmeticCommand + 1) := Fin.ofNat _ entryNum
  let initial := copyConfig (arithmeticInput.withPC (some entry))
  IO.println s!"HASH_ARITH_SETUP table_size={table.size} entry={entryNum} n=3 m=1 B=8 input_bits={(statsInitial initial).initialBits} fuel={fuel}"
  let t1 ← IO.monoMsNow
  let (finish,stats) := runInstrumented table initial fuel
  let t2 ← IO.monoMsNow
  let realFinal := finish.words.foldl (fun sum st => sum + st.length) 0
  IO.println s!"HASH_ARITH_COST halted={finish.pc.isNone} steps={stats.executed} initialBits={stats.initialBits} peakTotalBits={stats.peakTotalBits} peakSingleBits={stats.peakSingleBits} finalBits={stats.finalTotalBits} recountFinal={realFinal} distinctPC={stats.visitedDistinctLabels} tests={stats.tests} pushes={stats.push} pops={stats.pop} logic={stats.bitLogic} sets={stats.set} copies={stats.copy} peeks={stats.peek} gotos={stats.goto} halts={stats.halt} materialization_ms={t1-t0} instruction_ms={t2-t1}"
  IO.println s!"HASH_ARITH_NUMERIC dimension={(BinaryArithmetic.toNat (finish.words[0]!))} countM={(BinaryArithmetic.toNat (finish.words[1]!))} inputB={(BinaryArithmetic.toNat (finish.words[2]!))} output3m={(BinaryArithmetic.toNat (finish.words[14]!))} depthDenom={(BinaryArithmetic.toNat (finish.words[9]!))} loopCap={(BinaryArithmetic.toNat (finish.words[13]!))}"
  unless realFinal == stats.finalTotalBits do
    throw <| IO.userError "Mismatch actual vs delta-count total occupied bits"
  unless stats.executed == stats.set+stats.copy+stats.bitLogic+stats.tests+stats.push+stats.pop+stats.peek+stats.goto+stats.halt do
    throw <| IO.userError "Mismatch in opcode totals"

end IndependentNativeCost
