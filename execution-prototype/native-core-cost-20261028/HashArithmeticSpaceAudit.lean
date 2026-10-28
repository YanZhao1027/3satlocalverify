import HashArithmeticCases

/-! Independent physical stack-space accounting at EVERY executed prefix of
all six original arithmetic workloads. Unlike the incremental profiler, this
recounts the entire 22-stack store after each individual bit instruction.
The strict check detects a mistaken fast counter; the original full source
BitProgram.step final-state differential is a separate, stronger test. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 19000

def physicalSpace (c : CompactState l) : Nat × Nat :=
  c.words.foldl (fun acc w => (acc.1+w.length, max acc.2 w.length)) (0,0)

def independentPrefixAudit (table : Array (Instr 8 22 (StructuredCalls.size realArithmeticCommand + 1)))
    (entry : Fin (StructuredCalls.size realArithmeticCommand + 1))
    (n m B fuel : Nat) : Bool := Id.run do
  let input := copyConfig ((metadataInput n m B).withPC (some entry))
  let mut c := input
  let mut peak := physicalSpace c
  let mut executed := 0
  for _ in [:fuel] do
    let some pc := c.pc | break
    let some ins := table[pc.val]? | return false
    c := runOne ins c
    executed := executed + 1
    let current := physicalSpace c
    peak := (max peak.1 current.1, max peak.2 current.2)
  let (r, stats) := runInstrumented table input fuel
  return c.pc == r.pc && c.registers == r.registers && c.words == r.words &&
    stats.executed == executed &&
    stats.peakTotalBits == peak.1 && stats.peakSingleBits == peak.2 &&
    stats.finalTotalBits == (physicalSpace c).1

end IndependentNativeCost

def main : IO Unit := do
  let cmd := IndependentNativeCost.realArithmeticCommand
  let table := IndependentNonterminal.Linearize.instructionArray cmd
  let entryNum := IndependentNonterminal.Linearize.callEntry cmd 1 0
  let entry : Fin (OAI.Algorithms.SubexponentialSAT.StructuredCalls.size cmd + 1) := Fin.ofNat _ entryNum
  for (n,m,B) in ([(3,1,2),(3,1,4),(3,1,8),(3,2,8),(3,3,8),(8,5,8)] : List (Nat × Nat × Nat)) do
    let result := IndependentNativeCost.independentPrefixAudit table entry n m B 100000
    IO.println s!"HASH_PREFIX_PHYSICAL_AUDIT n={n} m={m} B={B} equal={result}"
    unless result do throw <| IO.userError "Discrepancy in every-prefix physically recounted occupied stack bits"
