import ReadyTerminalTrace
import TerminalBranchExecution

/-! For an actual fully LeafReady 3-variable physical input, this establishes
both original and executed surrogate have SAME output and SAME source bit
program trace length. The full original compiled code remains noncomputable;
we do not claim to have executed its high-query branch. -/
namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

/-- Standard valid and physically ready input for the original command. -/
theorem full_ready_emptyClause3 :
    DFSVisit.LeafReady 2 ((2:Nat).bits) 10
      ([[]] : DisjointReuse.RawCNF 3)
      (readyPhysicalState 3 2 2 [[false]]) := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro i hi
    have h258 : i ≠ (258 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h259 : i ≠ (259 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h264 : i ≠ (264 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h265 : i ≠ (265 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h267 : i ≠ (267 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    simp [readyPhysicalState, h258, h259, h264, h265, h267]

/-- The original unmodified `NativeLeafProgram.program 2` and the executable
terminal surrogate have BIT PROGRAM TRACES of equal length, not just matching
abstract #SAT results, on the real LeafReady empty formula input. -/
theorem full_native_and_proxy_same_trace_empty3 :
    ∃ t : Nat, ∃ b : State 80 1220,
      Trace (NativeLeafProgram.program 2) (t + 1)
        ((readyPhysicalState 3 2 2 []).withPC
          (some (NativeLeafProgram.program 2).entry))
        (b.withPC none) ∧
      Trace terminalProg (t + 1)
        ((readyPhysicalState 3 2 2 []).withPC (some terminalProg.entry))
        (b.withPC none) ∧
      b.stacks 263 = countWord 8 := by
  let a := readyPhysicalState 3 2 2 []
  let b := NativeTerminal.readyResult a 3 []
  have hb : a.stacks 265 = Encoding.encodeList id ([] : List (List Bool)) := by
    decide
  have hn : a.stacks 258 = Encoding.encodeNat 3 := by decide
  have hr : NativeTerminal.Ready a := by
    constructor
    · intro i hi
      have h258 : i ≠ (258 : Fin 1220) := by
        intro he; have := congrArg Fin.val he; omega
      have h259 : i ≠ (259 : Fin 1220) := by
        intro he; have := congrArg Fin.val he; omega
      have h264 : i ≠ (264 : Fin 1220) := by
        intro he; have := congrArg Fin.val he; omega
      have h265 : i ≠ (265 : Fin 1220) := by
        intro he; have := congrArg Fin.val he; omega
      have h267 : i ≠ (267 : Fin 1220) := by
        intro he; have := congrArg Fin.val he; omega
      simp [a, readyPhysicalState, h258, h259, h264, h265, h267]
    · simp [a, readyPhysicalState]
  obtain ⟨s, _, hfirst⟩ := NativeTerminal.readyCommand_eval a 3 [] hb hr hn
  have h0 : b.regs 0 = false := by
    simpa [b, NativeTerminal.clauseRecords] using
      (NativeTerminal.readyResult_empty_clause a
        ([] : List (List (SAT.Literal (Fin 3)))))
  have h7 : b.regs 7 = false := by
    simpa [b, NativeTerminal.clauseRecords] using
      (NativeTerminal.readyResult_nonempty a
        ([] : List (List (SAT.Literal (Fin 3)))))
  have hcount : b.stacks 263 = countWord 8 := by
    have h := NativeTerminal.readyResult_count a
      ([] : List (List (SAT.Literal (Fin 3)))) (Or.inr rfl)
    simpa [b, NativeTerminal.clauseRecords, ExecCNF.formulaSet] using h
  have horig := original_false_false 2 s a b hfirst h0 h7
  have hproxy := proxy_false_false s a b hfirst h0 h7
  refine ⟨s + 2, b, ?_, ?_, hcount⟩
  · exact StructuredCalls.compiled_halt_trace horig 265 263
  · exact StructuredCalls.compiled_halt_trace hproxy 265 263

end IndependentNativeExec
