import HashArithmeticCases

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 200000
  let cmd := IndependentNativeCost.realArithmeticCommand
  let table := IndependentNonterminal.Linearize.instructionArray cmd
  let entryNum := IndependentNonterminal.Linearize.callEntry cmd 1 0
  let entry : Fin (OAI.Algorithms.SubexponentialSAT.StructuredCalls.size cmd + 1) := Fin.ofNat _ entryNum
  IO.println s!"HASH_VARIANTS_SETUP staticSites={table.size} entry={entryNum} fuel={fuel}"
  for (n,m,B) in ([(3,1,2),(3,1,4),(3,1,8),(3,2,8),(3,3,8),(8,5,8)] : List (Nat × Nat × Nat)) do
    IndependentNativeCost.runCase table entry n m B fuel
