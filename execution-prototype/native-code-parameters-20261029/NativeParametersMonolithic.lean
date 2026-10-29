import NativeParametersPhysical

/-! One-PC single-HALT source-derived Lean bit-machine trace of the real
`NativeLeafSetup.canonicalStart` followed by the first full
`LeafOuterProgram.parameters` stage from original NativeCodeAssembly.command.
The local 8x77 original `CodeParametersProgram.program` is mapped by the
upstream original register+stack maps; the two route commands and final
cleanup are original OAI source instructions. An independent linker handles
only program labels/return PCs, NOT arithmetic or #SAT semantics.

The global equality to the entire upstream StructuredCalls.compiled code
remains UNPROVED; we check all stage-boundary state against genuine programs.
-/
namespace IndependentNativeParameters.Monolithic
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeStart
open IndependentNativeStart.CanonicalLinked
open IndependentNativeParameters
open IndependentNativeParameters.Physical

set_option maxRecDepth 24000

abbrev Total : Nat := 7201
abbrev CanonicalSource : Nat := 3161
abbrev InSource : Nat := 26
abbrev CoreSource : Nat := 1499
abbrev OutSource : Nat := 169
abbrev ClearSource : Nat := 2348

def bCanonical : Nat := 0
def bInputs : Nat := 3160
def bCore : Nat := bInputs+InSource
def bOutputs : Nat := bCore+CoreSource-1
def bCleanup : Nat := bOutputs+OutSource

private def global (j : Nat) : Fin Total := Fin.ofNat _ j

def inputCmd := routes parameterInputs
def outputCmd := routes parameterOutputs
def workerCmd := LeafProgram.Cleanup.Wide.command

def codeCanonical : Array (Instr 40 896 CanonicalSource) := monolithic

def codeInputs : Array (Instr 40 896 InSource) :=
  IndependentNonterminal.Linearize.instructionArray inputCmd

def codeCore : Array (Instr 8 77 CoreSource) := sourceOps

def codeOutputs : Array (Instr 40 896 OutSource) :=
  IndependentNonterminal.Linearize.instructionArray outputCmd

def codeCleanup : Array (Instr 40 768 ClearSource) :=
  IndependentNonterminal.FastLinearize.instructionArray workerCmd

def inputEntry : Nat := IndependentNonterminal.Linearize.callEntry inputCmd 1 0
def coreEntry : Nat := IndependentNonterminal.Linearize.callEntry ParamCmd 1 0
def outputEntry : Nat := IndependentNonterminal.Linearize.callEntry outputCmd 1 0
def cleanupEntry : Nat := IndependentNonterminal.Linearize.callEntry workerCmd 1 0

/-- Sequence stage compiler: omit old index 0, retarget all jumps to old
HALT 0 at the entry of the next source stage. -/
def seqStage (source : Array (Instr r s labels)) (base next : Nat)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896) :
    Array (Instr 40 896 Total) := Id.run do
  let mut out := #[]
  for j in [1:source.size] do
    let op := (source[j]?).getD Instr.halt
    out := out.push <| ProgramLinking.relocateInstr register stack
      (fun pc : Fin labels => global (if pc.val==0 then next else base+pc.val))
      (some (global next)) op
  return out

/-- .call stage compiler: keep old label 0 as a return slot. Its HALT
becomes GOTO next, and source jumps to local index 0 land on the slot. -/
def callStage (source : Array (Instr r s labels)) (base next : Nat)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896) :
    Array (Instr 40 896 Total) := Id.run do
  let mut out := #[]
  for j in [:source.size] do
    let op := (source[j]?).getD Instr.halt
    out := out.push <| ProgramLinking.relocateInstr register stack
      (fun pc : Fin labels => global (base+pc.val)) (some (global next)) op
  return out

def code : Array (Instr 40 896 Total) := Id.run do
  let mut out : Array (Instr 40 896 Total) := #[Instr.halt]
  out := out ++ seqStage codeCanonical bCanonical (bInputs+inputEntry) id id
  out := out ++ seqStage codeInputs bInputs (bCore+coreEntry) id id
  out := out ++ callStage codeCore bCore (bOutputs+outputEntry) regs8 stacks77
  out := out ++ seqStage codeOutputs bOutputs (bCleanup+cleanupEntry) id id
  out := out ++ callStage codeCleanup bCleanup 0 id
    (fun port : Fin 768 => Fin.castAdd 128 port)
  return out

def run (fuel : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let table := code
  IO.println s!"PARAM_MONOLITHIC_CODE actualLabels={table.size} expectedLabels={Total} firstInput={bInputs+inputEntry} firstCore={bCore+coreEntry} firstOutput={bOutputs+outputEntry} firstCleanup={bCleanup+cleanupEntry} originalParametersSites={StructuredCalls.size parameters}"
  (← IO.getStdout).flush
  unless table.size==Total &&
      codeInputs.size==InSource && codeCore.size==CoreSource &&
      codeOutputs.size==OutSource && codeCleanup.size==ClearSource &&
      StructuredCalls.size parameters==4040 do
    throw <| IO.userError "Linked program does not respect original 4040-site stage size"
  let e : Fin Total := Fin.ofNat _ 3
  let (result,stats) := runInstrumented table
    (copyConfig (loadedLocalInput.withPC (some e))) fuel
  let fin := bank result
  let validated := metadataCorrect 1 8 fin
  let finalTime ← IO.monoMsNow
  IO.println s!"PARAM_MONOLITHIC_RUN halted={result.pc.isNone} steps={stats.executed} peakStackBits={stats.peakTotalBits} longestStackBits={stats.peakSingleBits} visitedStaticPC={stats.visitedDistinctLabels} initialStackBits={stats.initialBits} finalStackBits={stats.finalTotalBits} verifiedFinalStackBits={bits fin} all768WorkerStacksEmpty={workerClean fin} all40RegistersClear={fin.regs.all (fun b=>!b)} original14MetadataCorrect={validated} instructionAndBuildMs={finalTime-t0}"
  IO.println s!"PARAM_MONOLITHIC_OUTPUT m={BinaryArithmetic.toNat (fin.words[782]!)} B={BinaryArithmetic.toNat (fin.words[786]!)} gapDenom={BinaryArithmetic.toNat (fin.words[800]!)} sevenBinary={((List.finRange 7).map (fun j => BinaryArithmetic.toNat (fin.words[801+j.val]!)))} sevenUnaryLengths={((List.finRange 7).map (fun j => (fin.words[808+j.val]!).length))}"
  (← IO.getStdout).flush
  unless result.pc.isNone && stats.executed == 19182 &&
      validated && workerClean fin && fin.regs.all (fun x => !x) &&
      stats.finalTotalBits==bits fin &&
      BinaryArithmetic.toNat (fin.words[782]!)==1 &&
      BinaryArithmetic.toNat (fin.words[786]!)==8 do
    throw <| IO.userError "Monolithic source parameter stage not source-faithful"
  IO.println "PARAMETERS_MONOLITHIC_SOURCE_SUCCESS 7201 labels, one terminal HALT, real nonempty CNF input"

end IndependentNativeParameters.Monolithic
