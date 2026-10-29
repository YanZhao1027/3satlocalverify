import NativeStartLinked

/-! Independent dual execution audit. Source stages are each executed from
source code with their exact original ABI ports; separately, the LINKED
single-PC program advances one instruction at a time. At all 4 source
command boundaries, check EVERY one of 40 register bits and EVERY one of 896
stacks, plus the exact next linked program counter. Also independently scan
896 stacks after EVERY one of the 6135 bit-program operations, verifying peak
occupied bits against the incremental linked instrumentation. -/
namespace IndependentNativeStart.LinkedAudit
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open IndependentNativeCost
open IndependentNativeCost.PhysicalStream
open IndependentNativeStart
open IndependentNativeStart.Linked

set_option maxRecDepth 24000

private def countBits (a : Array (List Bool)) : Nat :=
  a.foldl (fun n x => n + x.length) 0

private def countMaxStack (a : Array (List Bool)) : Nat :=
  a.foldl (fun n x => max n x.length) 0

def sourceReference :
    CompactState Clause × CompactState Hash × CompactState Cleanup × CompactState Save := Id.run do
  let clauseEntry : Fin Clause := Fin.ofNat _ clEntry
  let (a,_) := runInstrumented cl (copyConfig (loadedLocalInput.withPC (some clauseEntry))) 12000
  let he : Fin Hash := Fin.ofNat _ hashEntry
  let (b,_) := runFast hash (startCfg (takeFrame a) he) 12000
  let ce : Fin Cleanup := Fin.ofNat _ cleanupEntry
  let (c,_) := runInstrumented cleanup (startCfg (takeFrame b) ce) 12000
  let se : Fin Save := Fin.ofNat _ saveEntry
  let (d,_) := runInstrumented save (startCfg (takeFrame c) se) 12000
  return (a,b,c,d)

def runAudit : IO Unit := do
  let t0 ← IO.monoMsNow
  let (refClause, refHash, refWorker, refSave) := sourceReference
  unless refClause.pc.isNone && refHash.pc.isNone &&
    refWorker.pc.isNone && refSave.pc.isNone do
      throw <| IO.userError "Source stages not complete"
  let table := linked
  let init := copyConfig (loadedLocalInput.withPC (some (Fin.ofNat Total clEntry)))
  let mut c := init
  let mut maxTotal := countBits c.words
  let mut maxSingle := countMaxStack c.words
  let mut checked := 0
  let mut boundaries := 0
  for _ in [:12000] do
    let some pc := c.pc | break
    let some op := table[pc.val]? | throw <| IO.userError "Unknown linked label"
    c := runOne op c
    checked := checked + 1
    maxTotal := max maxTotal (countBits c.words)
    maxSingle := max maxSingle (countMaxStack c.words)
    let atBoundary :=
      if checked == 179 then
        some (refClause.registers,refClause.words,hashBase+hashEntry,"clause->hash")
      else if checked == 179+3585 then
        some (refHash.registers,refHash.words,cleanupBase+cleanupEntry,"hash->cleanup")
      else if checked == 179+3585+2348 then
        some (refWorker.registers,refWorker.words,saveBase+saveEntry,"cleanup->saveWidth")
      else if checked == 179+3585+2348+23 then
        some (refSave.registers,refSave.words,0,"final")
      else none
    if let some (regs,words,expectedPC,name) := atBoundary then
      let correctPC := if name == "final" then c.pc.isNone
        else c.pc == some (Fin.ofNat Total expectedPC)
      let good := c.registers == regs && c.words == words && correctPC
      IO.println s!"MONOLITHIC_BOUNDARY label={name} afterSteps={checked} exact40Regs896StacksAndPC={good} occupiedBits={countBits c.words}"
      (← IO.getStdout).flush
      unless good do throw <| IO.userError s!"Original staged vs monolithic state mismatch at {name}"
      boundaries := boundaries + 1
  let (compact,met) := runInstrumented table init 12000
  let success := c.pc.isNone && checked == 6135 && boundaries == 4 &&
    c.pc == compact.pc && c.registers == compact.registers &&
    c.words == compact.words && met.executed == checked &&
    maxTotal == met.peakTotalBits && maxSingle == met.peakSingleBits &&
    countBits c.words == met.finalTotalBits &&
    BinaryArithmetic.toNat (c.words[783]!) == 3
  IO.println s!"MONOLITHIC_SOURCE_BOUNDARY_AUDIT pass={success} executedSteps={checked} checkpoints={boundaries} occupiedDataPeak={maxTotal} longestStack={maxSingle} finalOccupied={countBits c.words} linkedStaticLabels={table.size} auditMs={(← IO.monoMsNow)-t0}"
  unless success do throw <| IO.userError "Monolithic source-boundary or full-stack cost audit failed"

end IndependentNativeStart.LinkedAudit

def main : IO Unit := IndependentNativeStart.LinkedAudit.runAudit
