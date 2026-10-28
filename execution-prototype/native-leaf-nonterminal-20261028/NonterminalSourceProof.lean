import NonterminalPrefixProbe
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCorrect

/-! True, nonempty, no-empty-clause CNF. Prove the ORIGINAL ready classifier
and actual leaf loader have an executable combined structured Eval path.
This theorem is intentionally about the prefix ONLY: the high-query suffix
is not run, and the final #SAT result is not claimed. -/
namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- This nontrivial input has precisely one positive unit clause and no
empty clause, unlike all previous terminal-path test fixtures. -/
theorem nonterminal_formula : F ≠ [] ∧ [] ∉ F := by decide

/-- The physical input is genuinely well-formed according to the ORIGINAL
native leaf input specification, including persistent context banks. -/
theorem actual_leaf_ready :
    DFSVisit.LeafReady 2 ((2 : Nat).bits) 10 F physical := by
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
      intro h; have := congrArg Fin.val h; omega
    have h259 : i ≠ (259 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    have h264 : i ≠ (264 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    have h265 : i ≠ (265 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    have h267 : i ≠ (267 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    simp [physical, IndependentNativeExec.readyPhysicalState,
      h258,h259,h264,h265,h267]

private theorem physical_terminal_ready : NativeTerminal.Ready physical := by
  constructor
  · intro i hi
    have h258 : i ≠ (258 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    have h259 : i ≠ (259 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    have h264 : i ≠ (264 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    have h265 : i ≠ (265 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    have h267 : i ≠ (267 : Fin 1220) := by
      intro h; have := congrArg Fin.val h; omega
    simp [physical, IndependentNativeExec.readyPhysicalState,
      h258,h259,h264,h265,h267]
  · decide

private theorem physical_bound : ∀ i : Fin 1220, (physical.stacks i).length ≤ 30 := by
  intro i
  simp only [physical, IndependentNativeExec.readyPhysicalState]
  split_ifs <;> decide

/-- The original ready stage classifies F as NONTERMINAL: it is neither an
empty-clause zero-count case nor an empty-formula power-of-two case. -/
theorem original_nonterminal_flags :
    (NativeTerminal.readyResult physical 3 (NativeTerminal.clauseRecords F)).regs 0 = false ∧
    (NativeTerminal.readyResult physical 3 (NativeTerminal.clauseRecords F)).regs 7 = true := by
  constructor
  · rw [NativeTerminal.readyResult_empty_clause]
    decide
  · rw [NativeTerminal.readyResult_nonempty]
    decide

/-- Both original source segments are truly executed before the still
noncomputable high-query invocation. The loader puts ORIGINAL encoded input
and context into its leaf ABI slots 1104, 1105, and 1106. -/
theorem original_nonterminal_prefix_executes :
    ∃ steps : Nat, ∃ finish : State 80 1220,
      Eval commonPrefix steps physical finish ∧
      finish.stacks 1104 = physical.stacks 265 ∧
      finish.stacks 1105 = physical.stacks 267 ∧
      finish.stacks 1106 = physical.stacks 264 ∧
      finish.stacks 1219 = [] := by
  let b := NativeTerminal.readyResult physical 3 (NativeTerminal.clauseRecords F)
  have hbody : physical.stacks 265 =
      Encoding.encodeList id (NativeTerminal.clauseRecords F) := by
    rfl
  have hn : physical.stacks 258 = Encoding.encodeNat 3 := by decide
  obtain ⟨s, hs, hclass⟩ :=
    NativeTerminal.readyCommand_eval physical 3
      (NativeTerminal.clauseRecords F) hbody physical_terminal_ready hn
  have hb : ∀ i : Fin 1220, (b.stacks i).length ≤ 30 := by
    intro i
    by_cases hi263 : i = (263 : Fin 1220)
    · subst i
      change ((NativeTerminal.result (NativeTerminal.prepared physical) 3
        (NativeTerminal.clauseRecords F)).stacks 263).length ≤ 30
      rw [NativeTerminal.result_nonterminal (NativeTerminal.prepared physical) F
        nonterminal_formula.2 nonterminal_formula.1]
      rw [NativeTerminal.classified_stacks]
      simp [NativeTerminal.prepared_output]
    by_cases hi268 : i = (268 : Fin 1220)
    · subst i
      simp [b]
    by_cases hi269 : i = (269 : Fin 1220)
    · subst i
      simp [b]
    rw [NativeTerminal.readyResult_frame physical 3
      (NativeTerminal.clauseRecords F) i hi263 hi268 hi269]
    exact physical_bound i
  obtain ⟨t, c, ht, hload, hcopy, hncopy, hocopy, hscratch, _, _, _, _⟩ :=
    Native.loadLeaf_eval b 30 hb
  have hc0 : b.regs 0 = false := original_nonterminal_flags.1
  have hc7 : b.regs 7 = true := original_nonterminal_flags.2
  have hskip : Eval (.base .skip : Cmd 80 1220) 0 c c :=
    Eval.base (StructuredProgram.Eval.skip c)
  have hbranch : Eval
      (.ite 0 (.base .skip)
        (.ite 7 (.seq Native.loadLeaf (.base .skip)) (.base .skip)))
      ((t + 0) + 1 + 1) b c :=
    Eval.ite_false hc0 (Eval.ite_true hc7 (Eval.seq hload hskip))
  have hp : Eval commonPrefix (s + ((t + 0) + 1 + 1)) physical c :=
    Eval.seq hclass hbranch
  refine ⟨_, c, hp, ?_, ?_, ?_, hscratch⟩
  · rw [hcopy]
    exact NativeTerminal.readyResult_frame physical 3
      (NativeTerminal.clauseRecords F) 265 (by decide) (by decide) (by decide)
  · rw [hncopy]
    exact NativeTerminal.readyResult_frame physical 3
      (NativeTerminal.clauseRecords F) 267 (by decide) (by decide) (by decide)
  · rw [hocopy]
    exact NativeTerminal.readyResult_frame physical 3
      (NativeTerminal.clauseRecords F) 264 (by decide) (by decide) (by decide)

/-- The finite original compiler preserves the concrete nonterminal
classification-and-leaf-loading prefix trace, plus its final copied input. -/
theorem original_nonterminal_compiled_prefix_trace :
    ∃ steps : Nat, ∃ finish : State 80 1220,
      BitProgram.Trace program (steps + 1)
        (physical.withPC (some program.entry)) (finish.withPC none) ∧
      finish.stacks 1104 = physical.stacks 265 ∧
      finish.stacks 1105 = physical.stacks 267 ∧
      finish.stacks 1106 = physical.stacks 264 ∧
      finish.stacks 1219 = [] := by
  obtain ⟨steps, finish, heval, hbody, hn, hm, hscratch⟩ :=
    original_nonterminal_prefix_executes
  exact ⟨steps, finish, StructuredCalls.compiled_halt_trace heval 265 263,
    hbody, hn, hm, hscratch⟩

/-- Independent mathematical oracle, NOT a substituted runtime answer. -/
theorem one_positive_unit_has_four_models :
    SAT.count (ExecCNF.formulaSet F) = 4 := by decide

end IndependentNonterminal
