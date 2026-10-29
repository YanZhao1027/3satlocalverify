import CompactNative40
import PhysicalPortMapProof
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHashParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgramFinal

/-! Original source opcode and physical-input exporter. Exports the genuine
Lean BitProgram.Instr constructors for the complete HashParametersProgram.ABI
and original LeafProgram.HashParameters 40x896 port maps, plus the entire
real physical state after executing ClauseCount.caller on a nonempty CNF.
This exports CODE AND INPUT ONLY, never #SAT answers nor an oracle. -/

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost

set_option maxRecDepth 18000
set_option maxHeartbeats 1000000

private def codeLine (i : Nat) (op : Instr 16 44 637) : String :=
  match op with
  | .halt => s!"OP|{i}|halt"
  | .goto pc => s!"OP|{i}|goto|{pc.val}"
  | .set dest val next => s!"OP|{i}|set|{dest.val}|{if val then 1 else 0}|{next.val}"
  | .copy dest src next => s!"OP|{i}|copy|{dest.val}|{src.val}|{next.val}"
  | .bnot dest src next => s!"OP|{i}|bnot|{dest.val}|{src.val}|{next.val}"
  | .band dest x y next => s!"OP|{i}|band|{dest.val}|{x.val}|{y.val}|{next.val}"
  | .bor dest x y next => s!"OP|{i}|bor|{dest.val}|{x.val}|{y.val}|{next.val}"
  | .bxor dest x y next => s!"OP|{i}|bxor|{dest.val}|{x.val}|{y.val}|{next.val}"
  | .branch test yes no => s!"OP|{i}|branch|{test.val}|{yes.val}|{no.val}"
  | .push port src next => s!"OP|{i}|push|{port.val}|{src.val}|{next.val}"
  | .peek port value present next => s!"OP|{i}|peek|{port.val}|{value.val}|{present.val}|{next.val}"
  | .pop port value present next => s!"OP|{i}|pop|{port.val}|{value.val}|{present.val}|{next.val}"

private def encodeBits (w : List Bool) : String :=
  String.intercalate "" (w.map (fun b => if b then "1" else "0"))

def main : IO Unit := do
  let c := LeafProgram.ClauseCount.caller
  let clauseTable : Array (Instr 40 896 (StructuredCalls.size c + 1)) :=
    IndependentNonterminal.Linearize.instructionArray c
  let entry : Fin (StructuredCalls.size c + 1) :=
    Fin.ofNat _ (IndependentNonterminal.Linearize.callEntry c 1 0)
  let (after,st) := runInstrumented clauseTable
    (copyConfig (loadedLocalInput.withPC (some entry))) 20000
  unless after.pc.isNone && st.executed == 180 &&
      BinaryArithmetic.toNat (after.words[782]!) == 1 do
    throw <| IO.userError "Real original ClauseCount.caller did not finish"
  IO.println s!"META|original-clauseCount-then-original-ABI|n3-m1-B8|clauses={st.executed}|peak={st.peakTotalBits}"
  (← IO.getStdout).flush
  for i in [:40] do
    if after.registers[i]! then IO.println s!"REG|{i}|1"
  IO.println "CHECKPOINT|reg-export-finished"
  (← IO.getStdout).flush
  for i in [:896] do
    let bits := after.words[i]!
    if !bits.isEmpty then IO.println s!"STACK|{i}|{encodeBits bits}"
  IO.println "CHECKPOINT|stack-export-finished"
  (← IO.getStdout).flush
  for i in [:16] do
    if h : i < 16 then
      IO.println s!"RMAP|{i}|{IndependentNativeCost.PhysicalPort.register ⟨i,h⟩}"
  IO.println "CHECKPOINT|register-map-finished"
  (← IO.getStdout).flush
  for i in [:44] do
    if h : i < 44 then
      IO.println s!"SMAP|{i}|{IndependentNativeCost.PhysicalPort.stack ⟨i,h⟩}"
  IO.println "CHECKPOINT|stack-map-finished"
  (← IO.getStdout).flush
  let cmd := HashParametersProgram.ABI.command
  let table : Array (Instr 16 44 (StructuredCalls.size cmd + 1)) :=
    IndependentNonterminal.Linearize.instructionArray cmd
  unless table.size == 637 do throw <| IO.userError "Expected 637 original ABI opcode positions"
  let sourceEntry := IndependentNonterminal.Linearize.callEntry cmd 1 0
  IO.println s!"TABLE|{table.size}|{sourceEntry}"
  (← IO.getStdout).flush
  for i in [:table.size] do
    IO.println (codeLine i ((table[i]?).getD Instr.halt))
    if i % 64 == 0 then (← IO.getStdout).flush
  IO.println "COMPLETE|original-lean-opcodes-and-physical-state"
