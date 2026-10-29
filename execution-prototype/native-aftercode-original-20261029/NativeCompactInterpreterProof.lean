import CompactNative40
/-! Kernel-checked universal interpreter bridge for every source BitProgram.Instr.
Uses standard Lean definitions without proof placeholders or extra axioms. -/

open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost

namespace IndependentNativeCompactProof

theorem get_ofFn_bang {α : Type} [Inhabited α] {n : Nat}
    (f : Fin n → α) (i : Fin n) :
    (Array.ofFn f)[i.val]! = f i := by
  simp

theorem ofFn_update {α : Type} {n : Nat} (f : Fin n → α)
    (i : Fin n) (value : α) :
    Array.ofFn (Function.update f i value) =
      (Array.ofFn f).set! i.val value := by
  apply Array.ext
  · simp
  · intro j hj₁ hj₂
    simp only [Array.size_ofFn] at hj₁
    by_cases h : j = i.val
    · subst j
      simp [Array.set!]
    · have different : (⟨j,hj₁⟩ : Fin n) ≠ i := by
        intro hEq
        exact h (congrArg Fin.val hEq)
      have hj : j < (Array.ofFn f).size := by simpa using hj₁
      have hsym : i.val ≠ j := Ne.symm h
      simp [Array.set!, Array.getElem_setIfInBounds hj, Function.update_noteq different, hsym]

end IndependentNativeCompactProof

namespace IndependentNativeCompactProof
theorem runOne_exact {r s l : Nat} (instr : Instr r s l) (cfg : Cfg r s l) :
    runOne instr (copyConfig cfg) = copyConfig (execInstr instr cfg) := by
  cases instr <;>
    simp [runOne, copyConfig, execInstr, readRegs, ofFn_update]
end IndependentNativeCompactProof
#print axioms IndependentNativeCompactProof.runOne_exact
