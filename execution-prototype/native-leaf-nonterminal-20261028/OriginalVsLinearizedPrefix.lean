import LinearizedPrefixRunner

/-! Runtime differential of the actual original `BitProgram.step program` and
our independent compact array evaluator on the SAME physical one-clause CNF.
Tests the COMPLETE register array, stack words array and program counter,
not merely the #SAT output or the number of steps. -/
namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 18000

def originalAfter (fuel : Nat) : Cfg 80 1220 (StructuredCalls.size commonPrefix + 1) :=
  (List.range fuel).foldl (fun c _ => (BitProgram.step program c).getD c)
    (physical.withPC (some program.entry))

def samePrefixState (fuel : Nat) : Bool := Id.run do
  let old := compactOf (originalAfter fuel)
  let new := (runCompact fuel).1
  return old.pc == new.pc && old.regs == new.regs && old.stackData == new.stackData

end IndependentNonterminal

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 40
  let pass := IndependentNonterminal.samePrefixState fuel
  IO.println s!"original_bitprogram_vs_compact_array_exact_state;steps={fuel};equal={pass}"
  if !pass then throw <| IO.userError "Mismatch in PC/registers/stacks"
