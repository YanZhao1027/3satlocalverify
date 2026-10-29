import NativeStartLinked

/-! Check REAL upstream `StructuredCalls.compiled LeafOuterProgram.start`
against independent 3036-label linker. This is an expensive source-code check;
fail on any mismatch and do not equate samples with a global theorem. -/
namespace IndependentNativeStart.OriginalCodeProbe
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open IndependentNativeStart.Linked

set_option maxRecDepth 22000
set_option maxHeartbeats 1000000

theorem original_source_labels :
    StructuredCalls.size LeafOuterProgram.start + 1 = Total := by decide

def source := StructuredCalls.compiled LeafOuterProgram.start 784 787

def originalInstruction (i : Fin Total) : Instr 40 896 Total :=
  let j : Fin (StructuredCalls.size LeafOuterProgram.start + 1) :=
    Fin.cast original_source_labels.symm i
  ProgramLinking.relocateInstr id id
    (fun x => Fin.cast original_source_labels x)
    none (source.code j)

def checkOne (i : Nat) : Bool :=
  if h : i < Total then
    let pos : Fin Total := ⟨i,h⟩
    (linked[i]?).getD Instr.halt == originalInstruction pos
  else false

end IndependentNativeStart.OriginalCodeProbe

def main (args : List String) : IO Unit := do
  let i := (args.head?.bind String.toNat?).getD 0
  IO.println s!"ORIGINAL_CODE_PROBE label={i}"
  (← IO.getStdout).flush
  let ok := IndependentNativeStart.OriginalCodeProbe.checkOne i
  IO.println s!"ORIGINAL_CODE_MATCH label={i} equal={ok}"
  unless ok do throw <| IO.userError "Original upstream compiled code disagrees"
