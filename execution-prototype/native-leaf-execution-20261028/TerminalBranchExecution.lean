import OriginalTerminalTraceProof

namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- A concrete ambient-number and clause-record state. Terminal processing
only reads these physical stacks and is independent of unused leaf banks. -/
def sourceInput (n : Nat) (records : List (List Bool)) : State 80 1220 :=
  ⟨(fun _ => false), fun i =>
    if i = (258 : Fin 1220) then Encoding.encodeNat n
    else if i = (265 : Fin 1220) then Encoding.encodeList id records
    else []⟩

theorem source_ready (n : Nat) (records : List (List Bool)) :
    NativeTerminal.Ready (sourceInput n records) := by
  constructor
  · intro i hi
    have h258 : i ≠ (258 : Fin 1220) := by
      intro hh
      have := congrArg Fin.val hh
      omega
    have h265 : i ≠ (265 : Fin 1220) := by
      intro hh
      have := congrArg Fin.val hh
      omega
    simp [sourceInput, h258, h265]
  · simp [sourceInput]

/-- The terminal-input physical source runs both the unmodified original
leaf command and its executable proxy with exactly the SAME source steps.
This holds for arbitrary ambient n and arbitrary k: the high-query branch
is skipped because the original classifier detects the empty formula. -/
theorem empty_formula_terminates (k n : Nat) :
    ∃ t : Nat,
      t ≤ 100 * ((Encoding.encodeList id ([] : List (List Bool))).length + 1) +
          11 * n + 33 ∧
      Eval (NativeLeafProgram.command k) t (sourceInput n [])
        (NativeTerminal.readyResult (sourceInput n []) n []) ∧
      Eval (NativeLeafDispatch.command (.base .skip)) t (sourceInput n [])
        (NativeTerminal.readyResult (sourceInput n []) n []) ∧
      (NativeTerminal.readyResult (sourceInput n []) n []).stacks 263 =
        countWord (2 ^ n) := by
  let a := sourceInput n []
  let b := NativeTerminal.readyResult a n []
  have hb : a.stacks 265 = Encoding.encodeList id ([] : List (List Bool)) := by
    simp [a, sourceInput]
  have hn : a.stacks 258 = Encoding.encodeNat n := by
    simp [a, sourceInput]
  obtain ⟨steps, ht, hrun⟩ :=
    NativeTerminal.readyCommand_eval a n [] hb (source_ready n []) hn
  have h0 : b.regs 0 = false := by
    simpa [b, NativeTerminal.clauseRecords] using
      (NativeTerminal.readyResult_empty_clause a
        ([] : List (List (SAT.Literal (Fin n)))))
  have h7 : b.regs 7 = false := by
    simpa [b, NativeTerminal.clauseRecords] using
      (NativeTerminal.readyResult_nonempty a
        ([] : List (List (SAT.Literal (Fin n)))))
  have hcount : b.stacks 263 = countWord (2 ^ n) := by
    have h := NativeTerminal.readyResult_count a
      ([] : List (List (SAT.Literal (Fin n)))) (Or.inr rfl)
    simpa [b, NativeTerminal.clauseRecords, ExecCNF.formulaSet] using h
  refine ⟨steps + 2, ?_, ?_, ?_, hcount⟩
  · simp [a, sourceInput] at ht
    simp [Encoding.encodeList] at ht ⊢
    omega
  · exact original_false_false k steps a b hrun h0 h7
  · exact proxy_false_false steps a b hrun h0 h7

/-- For a single empty clause, the same original and proxy programs both
terminate via one guard instruction and output the zero count word. -/
theorem empty_clause_terminates (k n : Nat) :
    ∃ t : Nat,
      Eval (NativeLeafProgram.command k) t
        (sourceInput n [[false]])
        (NativeTerminal.readyResult (sourceInput n [[false]]) n [[false]]) ∧
      Eval (NativeLeafDispatch.command (.base .skip)) t
        (sourceInput n [[false]])
        (NativeTerminal.readyResult (sourceInput n [[false]]) n [[false]]) := by
  let a := sourceInput n [[false]]
  let b := NativeTerminal.readyResult a n [[false]]
  have hb : a.stacks 265 = Encoding.encodeList id ([[false]] : List (List Bool)) := by
    simp [a, sourceInput]
  have hn : a.stacks 258 = Encoding.encodeNat n := by
    simp [a, sourceInput]
  obtain ⟨steps, _, hrun⟩ :=
    NativeTerminal.readyCommand_eval a n [[false]] hb (source_ready n [[false]]) hn
  have h0 : b.regs 0 = true := by
    have h := NativeTerminal.readyResult_empty_clause a
      ([[]] : List (List (SAT.Literal (Fin n))))
    have hrecs : NativeTerminal.clauseRecords
        ([[]] : List (List (SAT.Literal (Fin n)))) = [[false]] := by rfl
    rw [hrecs] at h
    simpa [b] using h
  exact ⟨steps+1, original_true k steps a b hrun h0,
    proxy_true steps a b hrun h0⟩

end IndependentNativeExec
