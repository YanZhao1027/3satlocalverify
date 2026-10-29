import CompactNative40
namespace NativeStepKernelProof
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost

theorem compact_halt_agrees {r s l : Nat} (c : Cfg r s l) :
    runOne (Instr.halt : Instr r s l) (copyConfig c) =
      copyConfig (execInstr (Instr.halt : Instr r s l) c) := by rfl

theorem compact_goto_agrees {r s l : Nat} (c : Cfg r s l) (dest : Fin l) :
    runOne (Instr.goto (r := r) (s := s) dest) (copyConfig c) =
      copyConfig (execInstr (Instr.goto (r := r) (s := s) dest) c) := by rfl

theorem ofFn_update {n : Nat} (f : Fin n → Bool) (pos : Fin n) (value : Bool) :
    (Array.ofFn f).setIfInBounds pos.val value =
      Array.ofFn (Function.update f pos value) := by
  apply Array.ext
  · simp
  · intro i hi hj
    have hbase : i < (Array.ofFn f).size := by
      simpa [Array.size_ofFn] using hj
    rw [Array.getElem_setIfInBounds (hj := hbase)]
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    by_cases h : pos.val = i
    · have heq : (⟨i, by simpa [Array.size_ofFn] using hj⟩ : Fin n) = pos := Fin.ext h.symm
      simp [h, heq]
    · have hne : (⟨i, by simpa [Array.size_ofFn] using hj⟩ : Fin n) ≠ pos := by
        intro eq
        exact h (congrArg Fin.val eq).symm
      simp [h, hne]

theorem compact_set_agrees {r s l : Nat} (c : Cfg r s l)
    (dest : Fin r) (value : Bool) (next : Fin l) :
    runOne (Instr.set (s := s) dest value next) (copyConfig c) =
      copyConfig (execInstr (Instr.set (s := s) dest value next) c) := by
  simp only [runOne, copyConfig, execInstr]
  congr 1
  exact ofFn_update c.regs dest value

end NativeStepKernelProof
#print axioms NativeStepKernelProof.compact_halt_agrees
#print axioms NativeStepKernelProof.compact_goto_agrees
#print axioms NativeStepKernelProof.compact_set_agrees
