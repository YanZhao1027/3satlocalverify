import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

/-! Executed ORIGINAL terminal classifier + count commands inside the exact
native leaf dispatcher syntax, with only the NEVER-TAKEN nonterminal leaf
replaced by skip. This is a terminal-branch surrogate, not executable full
NativeLeafProgram.command (which is noncomputable). The separate Lean proof
establishes same actual Eval path for the unmodified noncomputable command.
All counts are performed from the source BitProgram execInstr semantics. -/
namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000

/-- The exact upstream dispatch, with only the nonterminal branch replaced. -/
def terminalCmd : StructuredCalls.Cmd 80 1220 :=
  NativeLeafDispatch.command (.base .skip)

def terminalProg := StructuredCalls.compiled terminalCmd 265 263

/-- Empty formula input at ambient dimension n, before building realistic
persistent context words. Only accessed bits for the terminal command are set. -/
def emptyInput (n : Nat) : Cfg 80 1220 (StructuredCalls.size terminalCmd + 1) :=
  ⟨some terminalProg.entry, (fun _ => false), fun i =>
    if i = (258 : Fin 1220) then Encoding.encodeNat n
    else if i = (265 : Fin 1220) then Encoding.encodeList id ([] : List (List Bool))
    else []⟩

/-- Explicit record representing an empty clause, using the original encoding. -/
def emptyClauseInput (n : Nat) : Cfg 80 1220 (StructuredCalls.size terminalCmd + 1) :=
  ⟨some terminalProg.entry, (fun _ => false), fun i =>
    if i = (258 : Fin 1220) then Encoding.encodeNat n
    else if i = (265 : Fin 1220) then
      Encoding.encodeList id ([[false]] : List (List Bool))
    else []⟩

structure OpCounts where
  executed : Nat := 0
  booleanWrites : Nat := 0
  booleanLogic : Nat := 0
  sets : Nat := 0
  copies : Nat := 0
  nots : Nat := 0
  ands : Nat := 0
  ors : Nat := 0
  xors : Nat := 0
  guards : Nat := 0
  pushes : Nat := 0
  pops : Nat := 0
  peeks : Nat := 0
  gotos : Nat := 0
  halts : Nat := 0
  deriving Repr, Inhabited

structure Observation where
  cfg : Cfg 80 1220 (StructuredCalls.size terminalCmd + 1)
  operations : OpCounts
  initialStackBits : Nat
  currentStackBits : Nat
  peakStackBits : Nat
  peakStackLength : Nat

/-- Returns exact initial total stack bits and maximum stack word length. -/
def initStackStats
    (c : Cfg 80 1220 (StructuredCalls.size terminalCmd + 1)) : Nat × Nat :=
  (List.finRange 1220).foldl
    (fun acc i => (acc.1 + (c.stacks i).length, max acc.2 (c.stacks i).length)) (0, 0)

def start (c : Cfg 80 1220 (StructuredCalls.size terminalCmd + 1)) : Observation :=
  let s := initStackStats c
  ⟨c, {}, s.1, s.1, s.1, s.2⟩

/-- The actual p.code(pc) / BitProgram.execInstr operation on every step.
The only space-changing instruction variants are PUSH and POP. We track their
exact stack length deltas instead of scanning 1220 slots after every step. -/
def observeStep (o : Observation) : Observation := Id.run do
  let some pc := o.cfg.pc | return o
  let instr := terminalProg.code pc
  let mut ops := o.operations
  ops := { ops with executed := ops.executed + 1 }
  let mut total := o.currentStackBits
  let mut peakSingle := o.peakStackLength
  match instr with
  | .halt => ops := { ops with halts := ops.halts + 1 }
  | .goto _ => ops := { ops with gotos := ops.gotos + 1 }
  | .branch _ _ _ => ops := { ops with guards := ops.guards + 1 }
  | .set _ _ _ => ops := { ops with booleanWrites := ops.booleanWrites + 1, sets := ops.sets + 1 }
  | .copy _ _ _ => ops := { ops with booleanWrites := ops.booleanWrites + 1, copies := ops.copies + 1 }
  | .bnot _ _ _ => ops := { ops with booleanLogic := ops.booleanLogic + 1, nots := ops.nots + 1 }
  | .band _ _ _ _ => ops := { ops with booleanLogic := ops.booleanLogic + 1, ands := ops.ands + 1 }
  | .bor _ _ _ _ => ops := { ops with booleanLogic := ops.booleanLogic + 1, ors := ops.ors + 1 }
  | .bxor _ _ _ _ => ops := { ops with booleanLogic := ops.booleanLogic + 1, xors := ops.xors + 1 }
  | .push j _ _ =>
      ops := { ops with pushes := ops.pushes + 1 }
      total := total + 1
      peakSingle := max peakSingle ((o.cfg.stacks j).length + 1)
  | .pop j _ _ _ =>
      ops := { ops with pops := ops.pops + 1 }
      if !(o.cfg.stacks j).isEmpty then total := total - 1
  | .peek _ _ _ _ => ops := { ops with peeks := ops.peeks + 1 }
  let cfg' := execInstr instr o.cfg
  return ⟨cfg', ops, o.initialStackBits, total, max o.peakStackBits total, peakSingle⟩

/-- Fuel counts instruction slots, not wall-clock seconds. -/
def observeFuel (fuel : Nat) (c : Cfg 80 1220 (StructuredCalls.size terminalCmd + 1)) :=
  (List.range fuel).foldl (fun o _ => observeStep o) (start c)

structure Record where
  dimension : Nat
  kind : String
  halted : Bool
  instructions : Nat
  writes : Nat
  bitLogic : Nat
  sets : Nat
  copies : Nat
  nots : Nat
  ands : Nat
  ors : Nat
  xors : Nat
  tests : Nat
  pushes : Nat
  pops : Nat
  peeks : Nat
  gotos : Nat
  halts : Nat
  initialStackBits : Nat
  peakStackBits : Nat
  peakSingleStackBits : Nat
  finalStackBits : Nat
  resultWord : List Bool
  resultCount : Nat
  deriving Repr

def snapshot (n : Nat) (kind : String) (o : Observation) : Record :=
  ⟨n, kind, o.cfg.pc.isNone, o.operations.executed,
    o.operations.booleanWrites, o.operations.booleanLogic,
    o.operations.sets, o.operations.copies, o.operations.nots,
    o.operations.ands, o.operations.ors, o.operations.xors,
    o.operations.guards, o.operations.pushes, o.operations.pops,
    o.operations.peeks, o.operations.gotos, o.operations.halts,
    o.initialStackBits, o.peakStackBits, o.peakStackLength,
    o.currentStackBits, o.cfg.stacks 263,
    BinaryArithmetic.toNat (o.cfg.stacks 263)⟩

def emptyFormulaTrial (n fuel : Nat) : Record :=
  snapshot n "empty_formula" (observeFuel fuel (emptyInput n))

def emptyClauseTrial (n fuel : Nat) : Record :=
  snapshot n "empty_clause" (observeFuel fuel (emptyClauseInput n))

end IndependentNativeExec
