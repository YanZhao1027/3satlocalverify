import NativeCanonicalLinked
import NativeParametersCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramParameters

/-! STAGED physical execution of original LeafOuterProgram.parameters:
original input routes -> original CodeParametersProgram.fullCommand relocated
using original regs8/stacks77 -> original output routes -> original full worker
cleanup. We feed the *actual* final 40-register / 896-stack physical state
of the earlier, fully checked NativeLeafSetup.canonicalStart experiment.
The stage instruction traces are real; this is not yet one monolithic `.stage`
call and not a #SAT solver. -/
namespace IndependentNativeParameters.Physical
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeStart
open IndependentNativeStart.CanonicalLinked
open IndependentNativeParameters

set_option maxRecDepth 22000

structure Bank where
  regs : Array Bool
  words : Array (List Bool)

def bank (c : CompactState l) : Bank := ⟨c.registers,c.words⟩
def inject (b : Bank) (e : Fin l) : CompactState l := ⟨some e,b.regs,b.words⟩
def bits (b : Bank) : Nat := b.words.foldl (fun n w => n+w.length) 0

def workerClean (b : Bank) : Bool := Id.run do
  for i in [:768] do
    unless (b.words[i]!).isEmpty do return false
  return true

def coreRelocated : Array (Instr 40 896 Labels) :=
  sourceOps.map (fun op => ProgramLinking.relocateInstr regs8 stacks77 id none op)

def localView (b : Bank) (e : Fin Labels) : CompactState Labels :=
  ⟨some e, Array.ofFn (fun i : Fin 8 => b.regs[i.val]!),
   Array.ofFn (fun i : Fin 77 => b.words[i.val]!)⟩

def mappedSame (physical : Bank) (localResult : CompactState Labels) : Bool :=
  localResult.registers == Array.ofFn (fun i : Fin 8 => physical.regs[i.val]!) &&
  localResult.words == Array.ofFn (fun i : Fin 77 => physical.words[i.val]!)

def untouchedOutside (before after : Bank) : Bool := Id.run do
  for i in [8:40] do
    unless before.regs[i]! == after.regs[i]! do return false
  for i in [77:896] do
    unless before.words[i]! == after.words[i]! do return false
  return true

def metadataCorrect (m B : Nat) (b : Bank) : Bool := Id.run do
  if BinaryArithmetic.toNat (b.words[800]!) != SparseCode.gapDenom m B then return false
  for j in (List.finRange 7) do
    let expect := CodeParametersProgram.parameterValues m B j
    if BinaryArithmetic.toNat (b.words[801+j.val]!) != expect then return false
    if b.words[808+j.val]! != List.replicate expect true then return false
  return true

-- Connect the five actual source-level programs to the same physical memory.
def runFive (fuel : Nat) : IO Bank := do
  let t0 ← IO.monoMsNow
  let (cfg0,st0) := runInstrumented monolithic
    (copyConfig (loadedLocalInput.withPC (some (Fin.ofNat Full 3)))) fuel
  let b0 := bank cfg0
  IO.println s!"PHYSICAL_PARAM_CANONICAL halted={cfg0.pc.isNone} steps={st0.executed} m={BinaryArithmetic.toNat (b0.words[782]!)} B={BinaryArithmetic.toNat (b0.words[786]!)} dataBits={bits b0}"
  (← IO.getStdout).flush
  unless cfg0.pc.isNone && st0.executed==7085 && workerClean b0 do
    throw <| IO.userError "Canonical source input was not ready"

  let ci := routes parameterInputs
  let pi := IndependentNonterminal.Linearize.instructionArray ci
  let ei : Fin (StructuredCalls.size ci + 1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry ci 1 0)
  let (cfgi,sti) := runInstrumented pi (inject b0 ei) fuel
  let bi := bank cfgi
  IO.println s!"PHYSICAL_PARAM_INPUTS halted={cfgi.pc.isNone} steps={sti.executed} codeLabels={pi.size} inputM={BinaryArithmetic.toNat (bi.words[0]!)} inputB={BinaryArithmetic.toNat (bi.words[1]!)} peakBits={sti.peakTotalBits}"
  (← IO.getStdout).flush
  unless cfgi.pc.isNone && BinaryArithmetic.toNat (bi.words[0]!)==1 &&
    BinaryArithmetic.toNat (bi.words[1]!)==8 do
    throw <| IO.userError "Original physical input routes incorrect"

  let ec : Fin Labels := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry ParamCmd 1 0)
  let pc := coreRelocated
  let (cfgc,stc) := runInstrumented pc (inject bi ec) fuel
  let bc := bank cfgc
  let (localResult,loccost) := runInstrumented sourceOps (localView bi ec) fuel
  let consistent := cfgc.pc==localResult.pc && mappedSame bc localResult && untouchedOutside bi bc
  IO.println s!"PHYSICAL_PARAM_ORIGINAL_CORE halted={cfgc.pc.isNone} steps={stc.executed} localSteps={loccost.executed} innerLabels={sourceOps.size} mappedLabels={pc.size} fullMappedStateEqual={consistent} q={BinaryArithmetic.toNat (bc.words[5]!)} peakBits={stc.peakTotalBits}"
  (← IO.getStdout).flush
  unless cfgc.pc.isNone && stc.executed==loccost.executed && consistent &&
    BinaryArithmetic.toNat (bc.words[5]!)==1600 do
    throw <| IO.userError "Original parameter core mapping diverged"

  let co := routes parameterOutputs
  let po := IndependentNonterminal.Linearize.instructionArray co
  let eo : Fin (StructuredCalls.size co+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry co 1 0)
  let (cfgo,sto) := runInstrumented po (inject bc eo) fuel
  let bo := bank cfgo
  let okMetadata := metadataCorrect 1 8 bo
  IO.println s!"PHYSICAL_PARAM_OUTPUTS halted={cfgo.pc.isNone} steps={sto.executed} codeLabels={po.size} savedGapDenom={BinaryArithmetic.toNat (bo.words[800]!)} all14MetadataCorrect={okMetadata} peakBits={sto.peakTotalBits}"
  (← IO.getStdout).flush
  unless cfgo.pc.isNone && okMetadata do
    throw <| IO.userError "Original output routes did not produce expected metadata"

  let cc := LeafProgram.Cleanup.Wide.command
  let pp := IndependentNonterminal.FastLinearize.instructionArray cc
  let ee : Fin (StructuredCalls.size cc+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry cc 1 0)
  let dirtyBits := (List.range 768).foldl (fun n i => n+(bo.words[i]!).length) 0
  let (cfgf,stf) := runInstrumented pp (inject bo ee) fuel
  let bf := bank cfgf
  let finalMetadata := metadataCorrect 1 8 bf
  let expectedClear := 2*dirtyBits+2348
  IO.println s!"PHYSICAL_PARAM_CLEANUP halted={cfgf.pc.isNone} steps={stf.executed} sourceCostFormula={expectedClear} workerClean={workerClean bf} registersClear={bf.regs.all (fun b => !b)} metadataIntact={finalMetadata} peakBits={stf.peakTotalBits} finalDataBits={bits bf}"
  (← IO.getStdout).flush
  unless cfgf.pc.isNone && stf.executed==expectedClear && workerClean bf &&
    bf.regs.all (fun v => !v) && finalMetadata do
      throw <| IO.userError "Original physical worker cleanup incorrect"
  let total := st0.executed+sti.executed+stc.executed+sto.executed+stf.executed
  let peak := max st0.peakTotalBits (max sti.peakTotalBits
    (max stc.peakTotalBits (max sto.peakTotalBits stf.peakTotalBits)))
  IO.println s!"PHYSICAL_PARAMS_FIVE_STAGES_PASS sourceStepsIncludingFiveHalts={total} peakStackBits={peak} completeFromOriginalNonemptyCNF=true outputVerified=true internalWallMs={(← IO.monoMsNow)-t0}"
  (← IO.getStdout).flush
  return bf

end IndependentNativeParameters.Physical
