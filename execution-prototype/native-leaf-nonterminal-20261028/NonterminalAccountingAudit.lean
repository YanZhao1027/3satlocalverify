import LinearizedPrefixRunner

/-! Independent per-prefix accounting check for the nonterminal CNF. We
independently reconstruct actual physical occupied stack bits and max individual
stack size from all 1220 Array cells after EVERY step. The incremental
profiler must match both true peaks, final PC, all registers and all stack
contents. This uses same instruction decoding and execution, so it is NOT a
proof of array-compiler correctness (see original-vs-linearized differential).
-/
namespace IndependentNonterminal

set_option maxRecDepth 18000

def recount (words : Array (List Bool)) : Nat × Nat :=
  words.foldl (fun acc bits => (acc.1 + bits.length, max acc.2 bits.length))
    (0,0)

def auditAccounting (fuel : Nat) : Bool := Id.run do
  let init := physical.withPC (some program.entry)
  let mut a := compactOf init
  let start := recount a.stackData
  let mut peakTotal := start.1
  let mut peakSingle := start.2
  let mut executed := 0
  for _ in [:fuel] do
    let some pc := a.pc | break
    let some instr := fastArray[pc.val]? | return false
    a := executeCompact instr a
    executed := executed + 1
    let now := recount a.stackData
    peakTotal := max peakTotal now.1
    peakSingle := max peakSingle now.2
  let (b,s) := runCompactFrom init fuel
  return a.pc == b.pc && a.regs == b.regs && a.stackData == b.stackData &&
    s.peakTotalBits == peakTotal && s.peakSingleStackBits == peakSingle &&
    s.executed == executed && s.halted == a.pc.isNone

end IndependentNonterminal

#eval ("nonterminal_unit_4000", IndependentNonterminal.auditAccounting 4000)
