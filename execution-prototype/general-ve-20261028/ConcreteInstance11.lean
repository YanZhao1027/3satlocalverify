import Concrete2401
import GeneralVEDual11

namespace VerifiedReconstruction
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Executable algebraic operation callbacks match our theorem's represented
    ring operations DEFINITIONALLY, including their symbolic cost accounts. -/
theorem source_program_eq :
    (representedOps 2401).program = PaperKernel.ops 2401 := by rfl

/-- The literal OpenAI executable Reconstruction.run, fed with the same actual
    cached VE/Hermite jets as the run_memo_dual.sh CLI, exactly counts a genuine
    eleven-variable connected 3-CNF. No trust in native_decide is needed. -/
theorem eleven_input_original_CRT_exact :
    ((Reconstruction.run (PaperKernel.ops 2401)
      (fun i : Fin 3 => (i.val : ZMod 2401)) 7 4 2
      (fun i : Fin 3 =>
        let d := MemoVECNF.memoDualJet GeneralVEDual11.F (i.val : ZMod 2401)
        [d.fst, d.snd])).1.headD 0).val =
        SAT.count GeneralVEDual11.F := by
  have hcard : GeneralVEDual11.F.card < 3 * 2 := by decide
  have hmod : 2 ^ 11 < 2401 := by norm_num
  have h := concrete2401_count (Q := 3) GeneralVEDual11.F
    hcard (by omega) hmod
  rw [source_program_eq] at h
  exact h

end VerifiedReconstruction
