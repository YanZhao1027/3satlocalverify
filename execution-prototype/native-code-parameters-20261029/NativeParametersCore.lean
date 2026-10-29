import CompactNative40
import FastLinearizedCompiler
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgramUnary

/-! Execute the ORIGINAL CodeParametersProgram.fullCommand source arithmetic
on its real 8-register/77-stack bit VM, NOT an arithmetic replacement and
NOT a guessed metadata table. All 7 binary & 7 unary results are independently
checked against original mathematical specification AFTER source VM finishes. -/
namespace IndependentNativeParameters
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost

set_option maxRecDepth 22000

abbrev ParamCmd := CodeParametersProgram.fullCommand
abbrev Labels : Nat := StructuredCalls.size ParamCmd + 1

def sourceOps : Array (Instr 8 77 Labels) :=
  IndependentNonterminal.Linearize.instructionArray ParamCmd

def originalInput (m B : Nat) : StructuredCalls.State 8 77 :=
  ⟨fun _ => false, fun i =>
    if i = (0 : Fin 77) then m.bits
    else if i = (1 : Fin 77) then B.bits
    else []⟩

def runCore (m B fuel : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  let code := sourceOps
  let entryNum := IndependentNonterminal.Linearize.callEntry ParamCmd 1 0
  let entry : Fin Labels := Fin.ofNat _ entryNum
  IO.println s!"ORIGINAL_PARAMETERS_CORE_SETUP m={m} B={B} codeLabels={code.size} originalCodeLabels={Labels} entry={entryNum} fuel={fuel}"
  (← IO.getStdout).flush
  unless code.size == Labels do throw <| IO.userError "Source arithmetic opcode table invalid"
  let initial := copyConfig ((originalInput m B).withPC (some entry))
  let t0 ← IO.monoMsNow
  let (finish,st) := runInstrumented code initial fuel
  let t1 ← IO.monoMsNow
  let q := BinaryArithmetic.toNat (finish.words[5]!)
  let expectedQ := SparseCode.gapDenom m B
  let mut good := true
  for j in (List.finRange 7) do
    let actualBin := BinaryArithmetic.toNat (finish.words[(CodeParametersProgram.binaryPorts j).val]!)
    let actualUnary := finish.words[(CodeParametersProgram.unaryPorts j).val]!
    let expect := CodeParametersProgram.parameterValues m B j
    let equal := actualBin==expect && actualUnary==List.replicate expect true
    IO.println s!"ORIGINAL_PARAMETERS_CORE_VALUE j={j.val} bin={actualBin} unaryLength={actualUnary.length} expected={expect} correct={equal}"
    good := good && equal
  IO.println s!"ORIGINAL_PARAMETERS_CORE_RESULT halted={finish.pc.isNone} steps={st.executed} peakTotalStackBits={st.peakTotalBits} longestStack={st.peakSingleBits} initialBits={st.initialBits} finalBits={st.finalTotalBits} recountedFinal={finish.words.foldl (fun n w => n+w.length) 0} visitedLabels={st.visitedDistinctLabels} gapDenom={q} expectedGapDenom={expectedQ} allMetadataCorrect={good} executionMs={t1-t0} setupMs={t0-start}"
  (← IO.getStdout).flush
  unless finish.pc.isNone && m>0 && B>0 && good && q==expectedQ &&
    st.finalTotalBits == finish.words.foldl (fun n w => n+w.length) 0 do
      throw <| IO.userError "Actual source bit-VM parameter arithmetic not complete"

end IndependentNativeParameters
