import NativeCompactInterpreterProof
/-! Kernel-checked bounded execution semantics for exact ORIGINAL source
code tables, including List.finRange / map / toArray used by the experiment.
All n and all states; no finite test matrix or oracle in the proof. -/

open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeCompactProof

namespace IndependentNativeTraceProof

def sourceStep {r s l : Nat} (p : Program r s l) (c : Cfg r s l) : Cfg r s l :=
  match c.pc with
  | none => c
  | some pc => execInstr (p.code pc) c

def compactStep {r s l : Nat} (p : Program r s l) (c : CompactState l) : CompactState l :=
  match c.pc with
  | none => c
  | some pc => runOne (p.code pc) c

theorem step_exact {r s l : Nat} (p : Program r s l) (c : Cfg r s l) :
    compactStep p (copyConfig c) = copyConfig (sourceStep p c) := by
  cases h : c.pc with
  | none => simp [compactStep, sourceStep, copyConfig, h]
  | some pc =>
      simpa [compactStep, sourceStep, copyConfig, h] using (runOne_exact (p.code pc) c)

def sourceFuel {r s l : Nat} (p : Program r s l) : Nat → Cfg r s l → Cfg r s l
  | 0, c => c
  | n+1, c => sourceFuel p n (sourceStep p c)

def compactFuel {r s l : Nat} (p : Program r s l) : Nat → CompactState l → CompactState l
  | 0, c => c
  | n+1, c => compactFuel p n (compactStep p c)

theorem all_fuel_exact {r s l : Nat} (p : Program r s l) (n : Nat) (c : Cfg r s l) :
    compactFuel p n (copyConfig c) = copyConfig (sourceFuel p n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [compactFuel, sourceFuel]
      rw [step_exact, ih]

theorem bitStep_exact {r s l : Nat} (p : Program r s l) (c : Cfg r s l) :
    (OAI.Algorithms.SubexponentialSAT.BitProgram.step p c).map copyConfig =
      if c.pc.isSome then some (compactStep p (copyConfig c)) else none := by
  cases h : c.pc with
  | none => simp [OAI.Algorithms.SubexponentialSAT.BitProgram.step, h]
  | some pc =>
      simpa [OAI.Algorithms.SubexponentialSAT.BitProgram.step, compactStep, copyConfig, h] using
        (runOne_exact (p.code pc) c).symm

end IndependentNativeTraceProof
#print axioms IndependentNativeTraceProof.all_fuel_exact
#print axioms IndependentNativeTraceProof.bitStep_exact

namespace IndependentNativeTraceProof
theorem sourceArray_is_ofFn {r s l : Nat} (p : Program r s l) :
    ((List.finRange l).map (fun pc => p.code pc)).toArray = Array.ofFn p.code := by
  apply Array.ext
  · simp
  · intro i hi hj
    simp

theorem sourceArray_get {r s l : Nat} (p : Program r s l) (pc : Fin l) :
    (((List.finRange l).map (fun q => p.code q)).toArray[pc.val]?).getD Instr.halt =
      p.code pc := by
  simp [sourceArray_is_ofFn]
end IndependentNativeTraceProof

namespace IndependentNativeTraceProof

/-- This reads EXACTLY the List.finRange / List.map / Array.toArray form
used by the previous 8M-step direct-source experiment. -/
def directTableStep {r s l : Nat} (p : Program r s l) (c : CompactState l) :
    CompactState l :=
  match c.pc with
  | none => c
  | some pc =>
      runOne ((((List.finRange l).map (fun q => p.code q)).toArray[pc.val]?).getD Instr.halt) c

theorem directTableStep_eq_compactStep {r s l : Nat} (p : Program r s l)
    (c : CompactState l) : directTableStep p c = compactStep p c := by
  cases h : c.pc with
  | none => simp [directTableStep, compactStep, h]
  | some pc => simp [directTableStep, compactStep, h]

def directTableFuel {r s l : Nat} (p : Program r s l) : Nat → CompactState l → CompactState l
  | 0, c => c
  | n+1, c => directTableFuel p n (directTableStep p c)

theorem direct_table_fuel_exact {r s l : Nat} (p : Program r s l)
    (n : Nat) (c : Cfg r s l) :
    directTableFuel p n (copyConfig c) = copyConfig (sourceFuel p n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [directTableFuel, sourceFuel]
      rw [directTableStep_eq_compactStep, step_exact, ih]
end IndependentNativeTraceProof
#print axioms IndependentNativeTraceProof.sourceArray_is_ofFn
#print axioms IndependentNativeTraceProof.direct_table_fuel_exact
