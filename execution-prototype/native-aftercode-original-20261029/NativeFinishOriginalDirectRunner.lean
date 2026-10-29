import NativeFinishOriginalDirect

def main (args : List String) : IO Unit := do
  let chunk := (args[0]?.bind String.toNat?).getD 1000000
  let chunks := (args[1]?.bind String.toNat?).getD 8
  NativeFinishOriginalDirect.run chunk chunks
