import ReadyTerminalTrace

/-! Independent dynamic per-prefix validation of the incremental profiler.
For every executed BitProgram instruction, recompute physical stack-bit sums
and maximum stack lengths across ALL 1220 stacks from the actual resulting Cfg.
This catches a buggy delta counter instead of trusting reported peak values. -/
namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000

def sumOpCounts (c : OpCounts) : Nat :=
  c.sets + c.copies + c.nots + c.ands + c.ors + c.xors +
  c.guards + c.pushes + c.pops + c.peeks + c.gotos + c.halts

def auditAllPrefixes (fuel : Nat)
    (c : Cfg 80 1220 (StructuredCalls.size terminalCmd + 1)) : Bool := Id.run do
  let mut o := start c
  let mut ok := o.currentStackBits == dataBits o.cfg
  let mut peakTotal := o.initialStackBits
  let mut peakSingle := o.peakStackLength
  for _ in [:fuel] do
    if o.cfg.pc.isSome then
      o := observeStep o
      let stats := initStackStats o.cfg
      peakTotal := max peakTotal stats.1
      peakSingle := max peakSingle stats.2
      ok := ok && o.currentStackBits == stats.1
      ok := ok && o.currentStackBits == dataBits o.cfg
      ok := ok && o.peakStackBits == peakTotal
      ok := ok && o.peakStackLength == peakSingle
      ok := ok && o.operations.executed == sumOpCounts o.operations
  return ok && o.cfg.pc.isNone

#eval ("empty_3", auditAllPrefixes 300 (readyCfg 3 2 2 []))
#eval ("empty_5", auditAllPrefixes 300 (readyCfg 5 2 2 []))
#eval ("empty_clause_3", auditAllPrefixes 300 (readyCfg 3 2 2 [[false]]))

end IndependentNativeExec
