import NativeFinishOriginalDirect

/-! Finite differential tests: exact source BitProgram.execInstr vs the
compact array interpreter, on each upstream afterCode opcode and additional
synthetic opcode cases over four physical store configurations.  This is a
test matrix, not a universal semantic theorem. -/
namespace NativeFinishStepSemanticAudit

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open NativeFinishOriginalDirect

set_option maxRecDepth 25000
set_option maxHeartbeats 2000000

def sampleConfig (pc : Fin Total) (variant : Nat) : Cfg 40 896 Total :=
  ⟨some pc,
    fun reg => if variant == 0 then false else if variant == 1 then reg.val % 2 == 0
      else if variant == 2 then reg.val % 3 == 0 else true,
    fun stk => if variant == 0 then []
      else if variant == 1 then (if stk.val % 3 == 0 then [true] else [])
      else if variant == 2 then (if stk.val % 5 == 0 then [] else [false, true])
      else [true, false, true]⟩

def extra : Array (Instr 40 896 Total) :=
  #[.halt, .goto 1, .set 0 true 1, .set 1 false 1,
    .copy 0 1 1, .bnot 0 1 1, .band 0 1 2 1,
    .bor 0 1 2 1, .bxor 0 1 2 1, .branch 0 1 0,
    .push 0 1 1, .peek 0 0 1 1, .peek 1 0 0 1,
    .pop 0 0 1 1, .pop 1 0 0 1]

def check (opcode : Instr 40 896 Total) (pc : Fin Total) (variant : Nat) : Bool :=
  let cfg := sampleConfig pc variant
  let reference := copyConfig (execInstr opcode cfg)
  let actual := runOne opcode (copyConfig cfg)
  reference.pc == actual.pc &&
    reference.registers == actual.registers &&
    reference.words == actual.words

def run : IO Unit := do
  let table := originalCode
  let mut checks := 0
  for i in [:Total] do
    for v in [:4] do
      let pc : Fin Total := Fin.ofNat _ i
      unless check (table[i]?.getD Instr.halt) pc v do
        throw <| IO.userError s!"original instruction mismatch pc={i} case={v}"
      checks := checks+1
  for i in [:extra.size] do
    for v in [:4] do
      let pc : Fin Total := Fin.ofNat _ (i+1)
      unless check ((extra[i]?).getD Instr.halt) pc v do
        throw <| IO.userError s!"synthetic opcode mismatch index={i} case={v}"
      checks := checks+1
  IO.println s!"ORIGINAL_BITPROGRAM_COMPACT_STEP_DIFFERENTIAL_PASS cases={checks} originalLabels={Total} extraOpcodeCases={extra.size} physicalRegisters=40 physicalStacks=896"
end NativeFinishStepSemanticAudit
