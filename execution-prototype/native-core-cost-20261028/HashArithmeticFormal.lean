import MeasureHashArithmetic

/-! A genuine concrete instantiation of the ORIGINAL hash arithmetic
correctness + bit-program source steps bound. Here the bound is independent
of the original Lean interpreter and of the independent compact array runner.
This proves mathematical semantics, NOT that the 3006 observed program steps
are an asymptotic improvement over any optimized SAT solver. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- The finite original command, not our rewritten interpreter, computes
3m=3, sparse distance denominator=1280000 and loop cap=10 from n=3,m=1,B=8.
The theoretical source-Eval step bound is deliberately very conservative. -/
theorem native_original_hash_arithmetic_semantics :
    ∃ (steps : Nat) (finish : StructuredCalls.State 8 22),
      StructuredCalls.Eval realArithmeticCommand steps arithmeticInput finish ∧
      BinaryArithmetic.toNat (finish.stacks 14) = 3 ∧
      BinaryArithmetic.toNat (finish.stacks 9) = 1280000 ∧
      BinaryArithmetic.toNat (finish.stacks 13) = 10 ∧
      steps ≤ 6400000000 := by
  have hm : BinaryArithmetic.toNat (1 : Nat).bits ≠ 0 := by decide
  obtain ⟨t, rf, w, he, halpha, hdepth, hrounds, hword, ht⟩ :=
    HashParametersProgram.command_eval (fun _ => false)
      (3 : Nat).bits (1 : Nat).bits (8 : Nat).bits hm
  let b : StructuredCalls.State 8 22 := SubexpBlockParameterProgram.state rf w
  refine ⟨t, b, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [realArithmeticCommand, arithmeticInput] using he
  · have h14 : b.stacks 14 = w 14 := by rfl
    rw [h14]
    have one : BinaryArithmetic.toNat (1 : Nat).bits = 1 := by decide
    simpa only [one, Nat.mul_one] using halpha
  · have h9 : b.stacks 9 = w 9 := by rfl
    rw [h9]
    have hval : SparseCode.distanceDenom 1 8 = 1280000 := by decide
    have one : BinaryArithmetic.toNat (1 : Nat).bits = 1 := by decide
    have eight : BinaryArithmetic.toNat (8 : Nat).bits = 8 := by decide
    simpa only [one, eight, hval] using hdepth
  · have h13 : b.stacks 13 = w 13 := by rfl
    rw [h13]
    have hval : HashSelect.loopCap 3 1 = 10 := by decide
    have three : BinaryArithmetic.toNat (3 : Nat).bits = 3 := by decide
    have one : BinaryArithmetic.toNat (1 : Nat).bits = 1 := by decide
    simpa only [one, three, hval] using hrounds
  · have hval : 100000000 * HashParametersProgram.width
        (3 : Nat).bits (1 : Nat).bits (8 : Nat).bits ^ 2 = 6400000000 := by decide
    rw [hval] at ht
    exact ht

end IndependentNativeCost
