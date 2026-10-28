import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCode
import LinearizedCompiler

/-! An independent compact interpreter for ACTUAL BitProgram.Instr 40 896 L.
It keeps registers and all 896 stacks as arrays rather than dependent
function updates; the instruction opcode meanings directly mirror upstream
BitProgram.execInstr. No full interpreter-equivalence theorem is claimed.
The upstream module is untouched, and this is NEVER an oracle #SAT solver. -/

namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.BitProgram

structure CompactState (l : Nat) where
  pc : Option (Fin l)
  registers : Array Bool
  words : Array (List Bool)

def copyConfig {r s l : Nat} (c : Cfg r s l) : CompactState l :=
  ⟨c.pc, Array.ofFn c.regs, Array.ofFn c.stacks⟩

def runOne {r s l : Nat} (instr : Instr r s l) (c : CompactState l) : CompactState l :=
  match instr with
  | .halt => {c with pc := none}
  | .goto dest => {c with pc := some dest}
  | .set dest value next => {c with pc := some next, registers := c.registers.set! dest.val value}
  | .copy dest src next => {c with pc := some next, registers := c.registers.set! dest.val (c.registers[src.val]!)}
  | .bnot dest src next => {c with pc := some next, registers := c.registers.set! dest.val (!(c.registers[src.val]!))}
  | .band dest x y next => {c with pc := some next, registers := c.registers.set! dest.val ((c.registers[x.val]!) && (c.registers[y.val]!))}
  | .bor dest x y next => {c with pc := some next, registers := c.registers.set! dest.val ((c.registers[x.val]!) || (c.registers[y.val]!))}
  | .bxor dest x y next => {c with pc := some next, registers := c.registers.set! dest.val ((c.registers[x.val]!) ^^ (c.registers[y.val]!))}
  | .branch src yes no => {c with pc := some (if c.registers[src.val]! then yes else no)}
  | .push stack src next => {c with pc := some next, words := c.words.set! stack.val ((c.registers[src.val]!) :: (c.words[stack.val]!))}
  | .peek stack value present next =>
      let top := (c.words[stack.val]!).head?
      {c with pc := some next, registers :=
        (c.registers.set! value.val (top.getD false)).set! present.val top.isSome}
  | .pop stack value present next =>
      let top := (c.words[stack.val]!).head?
      {pc := some next,
       registers := (c.registers.set! value.val (top.getD false)).set! present.val top.isSome,
       words := c.words.set! stack.val (c.words[stack.val]!).tail}

structure Counters where
  executed : Nat := 0
  set : Nat := 0
  copy : Nat := 0
  bitLogic : Nat := 0
  tests : Nat := 0
  push : Nat := 0
  pop : Nat := 0
  peek : Nat := 0
  goto : Nat := 0
  halt : Nat := 0
  initialBits : Nat := 0
  peakTotalBits : Nat := 0
  peakSingleBits : Nat := 0
  finalTotalBits : Nat := 0
  visitedDistinctLabels : Nat := 0
  deriving Repr

def statsInitial {l : Nat} (c : CompactState l) : Counters :=
  let total := c.words.foldl (fun acc w => acc + w.length) 0
  let largest := c.words.foldl (fun acc w => max acc w.length) 0
  {initialBits := total, peakTotalBits := total, peakSingleBits := largest,
   finalTotalBits := total}

/-- Source-level instruction accounting with an explicit fuel budget. Every
push/pop adjusts total stack *data* bits, and every new maximal stack length
is recorded at the execution prefix. Code length & Lean RSS are separate. -/
def runInstrumented {r s l : Nat} (table : Array (Instr r s l))
    (input : CompactState l) (fuel : Nat) : CompactState l × Counters := Id.run do
  let mut c := input
  let mut met := statsInitial c
  let mut cache : Std.HashSet Nat := {}
  for _ in [:fuel] do
    let some pc := c.pc | break
    let some instr := table[pc.val]? | break
    cache := cache.insert pc.val
    let previous := c
    c := runOne instr c
    met := {met with executed := met.executed + 1}
    match instr with
    | .halt => met := {met with halt := met.halt + 1}
    | .goto _ => met := {met with goto := met.goto + 1}
    | .set _ _ _ => met := {met with set := met.set + 1}
    | .copy _ _ _ => met := {met with copy := met.copy + 1}
    | .bnot _ _ _ | .band _ _ _ _ | .bor _ _ _ _ | .bxor _ _ _ _ =>
        met := {met with bitLogic := met.bitLogic + 1}
    | .branch _ _ _ => met := {met with tests := met.tests + 1}
    | .push stack _ _ =>
        met := {met with push := met.push + 1, finalTotalBits := met.finalTotalBits + 1, peakSingleBits := max met.peakSingleBits ((previous.words[stack.val]!).length + 1)}
    | .pop stack _ _ _ =>
        met := {met with pop := met.pop + 1, finalTotalBits := met.finalTotalBits - (if (previous.words[stack.val]!).isEmpty then 0 else 1)}
    | .peek _ _ _ _ => met := {met with peek := met.peek + 1}
    met := {met with peakTotalBits := max met.peakTotalBits met.finalTotalBits}
  met := {met with visitedDistinctLabels := cache.size}
  return (c, met)

/-- The precondition input of the ORIGINAL native leaf startup (ABI local
stacks 784, 785 and 786). B=8 is the real local bound loaded from
M=2, clause width k=2; n=3 and one clause (x0). -/
def loadedLocalInput : StructuredCalls.State 40 896 :=
  ⟨fun _ => false, fun i =>
    if i = (784 : Fin 896) then
      Encoding.encodeList id (SqrtLogSpace.NativeTerminal.clauseRecords
        (IndependentNonterminal.F))
    else if i = 785 then (3 : Nat).bits
    else if i = 786 then (8 : Nat).bits
    else []⟩

/-- Number of input data bits, independent of program code. -/
def loadedInputBits : Nat :=
  (List.finRange 896).foldl (fun sum i => sum + (loadedLocalInput.stacks i).length) 0

end IndependentNativeCost
