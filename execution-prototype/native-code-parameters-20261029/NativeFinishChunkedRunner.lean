import NativeFinishChunked

def main (args : List String) : IO Unit := do
  let chunkSize := (args[0]?.bind String.toNat?).getD 2000000
  let chunks := (args[1]?.bind String.toNat?).getD 2
  IndependentNativeParameters.FinishChunked.run chunkSize chunks
