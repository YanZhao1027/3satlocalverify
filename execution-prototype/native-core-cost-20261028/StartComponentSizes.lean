import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCode

namespace CostNativeStart
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram

def main : IO Unit := do
  IO.println s!"ORIGINAL_CLAUSE_COUNT_SITES {StructuredCalls.size LeafProgram.ClauseCount.caller}"
  IO.println s!"ORIGINAL_PREPARE_HASH_SITES {StructuredCalls.size prepareHash}"
  IO.println s!"ORIGINAL_SAVE_WIDTH_SITES {StructuredCalls.size saveWidth}"
  IO.println s!"ORIGINAL_START_SITES {StructuredCalls.size start}"
end CostNativeStart

def main : IO Unit := CostNativeStart.main
