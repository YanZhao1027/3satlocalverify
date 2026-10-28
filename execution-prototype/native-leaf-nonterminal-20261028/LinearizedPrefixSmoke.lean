import LinearizedPrefixRunner

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 5000
  IO.println (IndependentNonterminal.summary fuel)
