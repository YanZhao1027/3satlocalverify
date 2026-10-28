import NonterminalPrefixProbe

/-! The true ORIGINAL NativeTerminal.command and bit-level Program, executed
with a valid, one-clause, nonempty 3-CNF physical input. This is the actual
nonterminal SELECTOR path, not a mock continuation and not the high query. -/
namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 10000

def classifierProgram := NativeTerminal.program

def classifierInput : Cfg 80 1220 (StructuredCalls.size NativeTerminal.command + 1) :=
  physical.withPC (some classifierProgram.entry)

structure ClassRun where
  steps : Nat
  halted : Bool
  zeroClause : Bool
  hasFormula : Bool
  initialBits : Nat
  peakBits : Nat
  peakSingle : Nat
  resultLen : Nat
  copiedBody : Bool
  deriving Repr

/-- Counts all executed bit-source instructions, including final HALT.
For each prefix independently recomputes stack usage from all 1220 stacks. -/
def runClassification (fuel : Nat) : ClassRun := Id.run do
  let mut c := classifierInput
  let mut count := 0
  let mut peak := (List.finRange 1220).foldl (fun s i => s + (c.stacks i).length) 0
  let initial := peak
  let mut peakSingle := (List.finRange 1220).foldl (fun s i => max s (c.stacks i).length) 0
  for _ in [:fuel] do
    if c.pc.isSome then
      c := (BitProgram.step classifierProgram c).getD c
      count := count + 1
      let total := (List.finRange 1220).foldl (fun s i => s + (c.stacks i).length) 0
      peak := max peak total
      peakSingle := max peakSingle
        ((List.finRange 1220).foldl (fun s i => max s (c.stacks i).length) 0)
  return ⟨count, c.pc.isNone, c.regs 0, c.regs 7, initial,
    peak, peakSingle, (c.stacks 263).length,
    c.stacks 265 == physical.stacks 265⟩

end IndependentNonterminal
