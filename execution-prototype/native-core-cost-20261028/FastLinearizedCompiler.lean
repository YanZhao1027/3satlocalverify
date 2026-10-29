import LinearizedCompiler

/-! Tail/difference-list form of the independently constructed source opcode
linearizer. Unlike `LinearizedCompiler.callCode`, this version does not use
recursive `List.append` at each `.seq` / `.ite`, avoiding quadratic copying
on large nested commands. Every opcode is still an original `BitProgram.Instr`.
Static code equivalence remains a separate audit obligation. -/
namespace IndependentNonterminal.FastLinearize
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.StructuredProgram
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

variable {r s l : Nat} [NeZero l]

private def site (i : Nat) : Fin l := Fin.ofNat l i

open IndependentNonterminal.Linearize (baseEntry callEntry)

def baseCodeD : StructuredProgram.Cmd r s → Nat → Nat → List (Instr r s l) → List (Instr r s l)
  | .skip, _, _, tail => tail
  | .atom a, _, exit, tail => a.instr (site exit) :: tail
  | .seq a b, start, exit, tail =>
      baseCodeD a start (baseEntry b (start + StructuredProgram.size a) exit)
        (baseCodeD b (start + StructuredProgram.size a) exit tail)
  | .ite test yes no, start, exit, tail =>
      let ys := start + 1
      let ns := ys + StructuredProgram.size yes
      Instr.branch test (site (baseEntry yes ys exit))
        (site (baseEntry no ns exit)) ::
        baseCodeD yes ys exit (baseCodeD no ns exit tail)
  | .while test body, start, exit, tail =>
      Instr.branch test (site (baseEntry body (start + 1) start)) (site exit) ::
        baseCodeD body (start + 1) start tail

def callCodeD : StructuredCalls.Cmd r s → Nat → Nat → List (Instr r s l) → List (Instr r s l)
  | .base b, start, exit, tail => baseCodeD b start exit tail
  | .call p, start, exit, tail =>
      ((List.finRange _).map (fun q =>
        ProgramLinking.relocateInstr id id (fun i => site (start + i.val))
          (some (site exit)) (p.code q))) ++ tail
  | .seq a b, start, exit, tail =>
      callCodeD a start (callEntry b (start + StructuredCalls.size a) exit)
        (callCodeD b (start + StructuredCalls.size a) exit tail)
  | .ite test yes no, start, exit, tail =>
      let ys := start + 1
      let ns := ys + StructuredCalls.size yes
      Instr.branch test (site (callEntry yes ys exit))
        (site (callEntry no ns exit)) ::
        callCodeD yes ys exit (callCodeD no ns exit tail)
  | .while test body, start, exit, tail =>
      Instr.branch test (site (callEntry body (start + 1) start)) (site exit) ::
        callCodeD body (start + 1) start tail

theorem baseCodeD_length (c : StructuredProgram.Cmd r s) (start exit : Nat)
    (tail : List (Instr r s l)) :
    (baseCodeD (l := l) c start exit tail).length = StructuredProgram.size c + tail.length := by
  induction c generalizing start exit tail with
  | skip => simp [baseCodeD, StructuredProgram.size]
  | atom a => simp [baseCodeD, StructuredProgram.size, Nat.add_comm]
  | seq a b ihA ihB =>
      change (baseCodeD a start (baseEntry b (start + StructuredProgram.size a) exit)
        (baseCodeD b (start + StructuredProgram.size a) exit tail)).length = _
      calc
        _ = StructuredProgram.size a +
            (baseCodeD b (start + StructuredProgram.size a) exit tail).length :=
          ihA _ _ _
        _ = StructuredProgram.size a +
            (StructuredProgram.size b + tail.length) := by rw [ihB]
        _ = StructuredProgram.size (.seq a b) + tail.length := by
          simp [StructuredProgram.size, Nat.add_assoc]
  | ite test yes no ihYes ihNo =>
      change (Instr.branch test (site (baseEntry yes (start+1) exit))
        (site (baseEntry no (start+1+StructuredProgram.size yes) exit)) ::
        baseCodeD yes (start+1) exit
          (baseCodeD no (start+1+StructuredProgram.size yes) exit tail)).length = _
      simp only [List.length_cons]
      rw [ihYes, ihNo]
      simp only [StructuredProgram.size]
      omega
  | «while» test body ih =>
      change (Instr.branch test (site (baseEntry body (start+1) start)) (site exit) ::
        baseCodeD body (start+1) start tail).length = _
      simp only [List.length_cons]
      rw [ih]
      simp only [StructuredProgram.size]
      omega

theorem callCodeD_length (c : StructuredCalls.Cmd r s) (start exit : Nat)
    (tail : List (Instr r s l)) :
    (callCodeD (l := l) c start exit tail).length = StructuredCalls.size c + tail.length := by
  induction c generalizing start exit tail with
  | base b => exact baseCodeD_length b start exit tail
  | call p =>
      simp only [callCodeD, List.length_append, List.length_map, List.length_finRange,
        StructuredCalls.size]
  | seq a b ihA ihB =>
      change (callCodeD a start (callEntry b (start + StructuredCalls.size a) exit)
        (callCodeD b (start + StructuredCalls.size a) exit tail)).length = _
      calc
        _ = StructuredCalls.size a +
            (callCodeD b (start + StructuredCalls.size a) exit tail).length :=
          ihA _ _ _
        _ = StructuredCalls.size a +
            (StructuredCalls.size b + tail.length) := by rw [ihB]
        _ = StructuredCalls.size (.seq a b) + tail.length := by
          simp [StructuredCalls.size, Nat.add_assoc]
  | ite test yes no ihYes ihNo =>
      change (Instr.branch test (site (callEntry yes (start+1) exit))
        (site (callEntry no (start+1+StructuredCalls.size yes) exit)) ::
        callCodeD yes (start+1) exit
          (callCodeD no (start+1+StructuredCalls.size yes) exit tail)).length = _
      simp only [List.length_cons]
      rw [ihYes, ihNo]
      simp only [StructuredCalls.size]
      omega
  | «while» test body ih =>
      change (Instr.branch test (site (callEntry body (start+1) start)) (site exit) ::
        callCodeD body (start+1) start tail).length = _
      simp only [List.length_cons]
      rw [ih]
      simp only [StructuredCalls.size]
      omega

def instructionArray (c : StructuredCalls.Cmd r s) : Array (Instr r s l) :=
  (Instr.halt :: callCodeD c 1 0 []).toArray

theorem instructionArray_size (c : StructuredCalls.Cmd r s) :
    (instructionArray (l := l) c).size = StructuredCalls.size c + 1 := by
  simp [instructionArray, callCodeD_length]

end IndependentNonterminal.FastLinearize
