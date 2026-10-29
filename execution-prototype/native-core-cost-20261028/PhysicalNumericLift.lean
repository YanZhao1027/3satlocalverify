import MeasurePhysicalHash40Stream

/-! Low-overhead, source-semantics-preserving physical execution. Compiled
`ProgramLinking.relocateInstr` creates large dependent Fin values repeatedly
at each step. We instead use the same original register/stack maps ONLY to
index the physical arrays, retaining original source-PC and instruction data.
The one-op refinement theorem below is kernel checked for *all* BitProgram
instruction constructors, not a selected opcode or SAT output check. -/
namespace IndependentNativeCost.PhysicalStream
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog

set_option maxRecDepth 18000

def regPort (i : Fin 16) : Nat := PhysicalPort.register i
def stackPort (i : Fin 44) : Nat := PhysicalPort.stack i

/-- Original BitProgram opcode meaning on the physical 40 x 896 bit store.
No retargeting of formula data; only original ABI port map is used. -/
def physicalNumericOne (instr : Instr 16 44 L) (c : CompactState L) : CompactState L :=
  match instr with
  | .halt => {c with pc := none}
  | .goto dest => {c with pc := some dest}
  | .set dest value next =>
      {c with pc := some next, registers := c.registers.set! (regPort dest) value}
  | .copy dest src next =>
      {c with pc := some next, registers := c.registers.set! (regPort dest) (c.registers[regPort src]!)}
  | .bnot dest src next =>
      {c with pc := some next, registers := c.registers.set! (regPort dest) (!(c.registers[regPort src]!))}
  | .band dest x y next =>
      {c with pc := some next, registers := c.registers.set! (regPort dest) ((c.registers[regPort x]!) && (c.registers[regPort y]!))}
  | .bor dest x y next =>
      {c with pc := some next, registers := c.registers.set! (regPort dest) ((c.registers[regPort x]!) || (c.registers[regPort y]!))}
  | .bxor dest x y next =>
      {c with pc := some next, registers := c.registers.set! (regPort dest) ((c.registers[regPort x]!) ^^ (c.registers[regPort y]!))}
  | .branch src yes no => {c with pc := some (if c.registers[regPort src]! then yes else no)}
  | .push port src next =>
      {c with pc := some next, words := c.words.set! (stackPort port) ((c.registers[regPort src]!) :: (c.words[stackPort port]!))}
  | .peek port value present next =>
      let head := (c.words[stackPort port]!).head?
      {c with pc := some next, registers := (c.registers.set! (regPort value) (head.getD false)).set! (regPort present) head.isSome}
  | .pop port value present next =>
      let head := (c.words[stackPort port]!).head?
      {pc := some next, registers := (c.registers.set! (regPort value) (head.getD false)).set! (regPort present) head.isSome, words := c.words.set! (stackPort port) (c.words[stackPort port]!).tail}

/-- General, compositional source-opcode refinement: the numerical mapping
executes IDENTICALLY to actual upstream ProgramLinking.relocateInstr on every
possible source instruction and any compatible physical array state. -/
theorem physicalNumericOne_refines_original (op : Instr 16 44 L) (cfg : CompactState L) :
    physicalNumericOne op cfg = runOne (liftSource op) cfg := by
  cases op <;>
    simp [physicalNumericOne, runOne, liftSource, regPort, stackPort,
      PhysicalPort.register_exact, PhysicalPort.stack_exact, ProgramLinking.relocateInstr]

/-- A truly executed bit-transition stream, no source code materialization
or precomputed answer, with explicit push/pop/branch subtype counts. -/
def runFast (table : Array (Instr 16 44 L))
    (start : CompactState L) (fuel : Nat) : CompactState L × Counters := Id.run do
  let mut c := start
  let mut stat := statsInitial c
  let mut used : Std.HashSet Nat := {}
  for _ in [:fuel] do
    let some pc := c.pc | break
    let some op := table[pc.val]? | break
    used := used.insert pc.val
    let prev := c
    c := physicalNumericOne op c
    stat := {stat with executed := stat.executed + 1}
    match op with
    | .halt => stat := {stat with halt := stat.halt + 1}
    | .goto _ => stat := {stat with goto := stat.goto + 1}
    | .set _ _ _ => stat := {stat with set := stat.set + 1}
    | .copy _ _ _ => stat := {stat with copy := stat.copy + 1}
    | .bnot _ _ _ | .band _ _ _ _ | .bor _ _ _ _ | .bxor _ _ _ _ =>
        stat := {stat with bitLogic := stat.bitLogic + 1}
    | .branch _ _ _ => stat := {stat with tests := stat.tests + 1}
    | .push port _ _ =>
        stat := {stat with push := stat.push + 1, finalTotalBits := stat.finalTotalBits + 1, peakSingleBits := max stat.peakSingleBits ((prev.words[stackPort port]!).length + 1)}
    | .pop port _ _ _ =>
        stat := {stat with pop := stat.pop + 1, finalTotalBits := stat.finalTotalBits - (if (prev.words[stackPort port]!).isEmpty then 0 else 1)}
    | .peek _ _ _ _ => stat := {stat with peek := stat.peek + 1}
    stat := {stat with peakTotalBits := max stat.peakTotalBits stat.finalTotalBits}
  return (c, {stat with visitedDistinctLabels := used.size})

end IndependentNativeCost.PhysicalStream
