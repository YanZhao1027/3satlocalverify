import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

/-! Proof that the fully original noncomputable NativeLeafProgram.command
executes EXACTLY the same terminal path as a computable dispatcher surrogate.
The unused high-query program never needs reduction. -/

namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- The original complete native command has the same steps on the two-false
terminal path. No replacement in this theorem's program expression. -/
theorem original_false_false (k steps : Nat)
    (a b : State 80 1220)
    (first : Eval NativeTerminal.readyCommand steps a b)
    (h0 : b.regs 0 = false) (h7 : b.regs 7 = false) :
    Eval (NativeLeafProgram.command k) (steps + 2) a b := by
  let q : Cmd 80 1220 :=
    NativeLeafExecution.command (NativeLeafProgram.localCommand k)
  change Eval (NativeLeafDispatch.command q) (steps + 2) a b
  rw [NativeLeafDispatch.command]
  have hs : Eval (.base .skip : Cmd 80 1220) 0 b b :=
    Eval.base (StructuredProgram.Eval.skip b)
  exact Eval.seq first (Eval.ite_false h0 (Eval.ite_false h7 hs))

/-- The original full native command also has the same single-guard terminal
path when the input contains an empty clause. -/
theorem original_true (k steps : Nat) (a b : State 80 1220)
    (first : Eval NativeTerminal.readyCommand steps a b)
    (h0 : b.regs 0 = true) :
    Eval (NativeLeafProgram.command k) (steps + 1) a b := by
  let q : Cmd 80 1220 :=
    NativeLeafExecution.command (NativeLeafProgram.localCommand k)
  change Eval (NativeLeafDispatch.command q) (steps + 1) a b
  rw [NativeLeafDispatch.command]
  have hs : Eval (.base .skip : Cmd 80 1220) 0 b b :=
    Eval.base (StructuredProgram.Eval.skip b)
  exact Eval.seq first (Eval.ite_true h0 hs)

/-- A computable terminal proxy follows the SAME two-false instruction path,
including identical source-level step count and final state. -/
theorem proxy_false_false (steps : Nat) (a b : State 80 1220)
    (first : Eval NativeTerminal.readyCommand steps a b)
    (h0 : b.regs 0 = false) (h7 : b.regs 7 = false) :
    Eval (NativeLeafDispatch.command (.base .skip)) (steps + 2) a b := by
  change Eval (.seq NativeTerminal.readyCommand
    (.ite 0 (.base .skip) (.ite 7 (.base .skip) (.base .skip)))) (steps + 2) a b
  have hs : Eval (.base .skip : Cmd 80 1220) 0 b b :=
    Eval.base (StructuredProgram.Eval.skip b)
  exact Eval.seq first (Eval.ite_false h0 (Eval.ite_false h7 hs))

/-- Similarly for the one-guard true terminal branch. -/
theorem proxy_true (steps : Nat) (a b : State 80 1220)
    (first : Eval NativeTerminal.readyCommand steps a b)
    (h0 : b.regs 0 = true) :
    Eval (NativeLeafDispatch.command (.base .skip)) (steps + 1) a b := by
  change Eval (.seq NativeTerminal.readyCommand
    (.ite 0 (.base .skip) (.ite 7 (.base .skip) (.base .skip)))) (steps + 1) a b
  have hs : Eval (.base .skip : Cmd 80 1220) 0 b b :=
    Eval.base (StructuredProgram.Eval.skip b)
  exact Eval.seq first (Eval.ite_true h0 hs)

end IndependentNativeExec
