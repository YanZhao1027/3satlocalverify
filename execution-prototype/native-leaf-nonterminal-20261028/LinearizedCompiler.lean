import NonterminalPrefixProbe

/-! Independently implemented linear-site compiler. Every emitted operation
is an ORIGINAL BitProgram.Instr; each source call is relocated using ORIGINAL
ProgramLinking.relocateInstr. A separate exhaustive toy differential and
selected-label differential check are required before using this as evidence.
No correctness theorem for all possible Cmd values is claimed yet. -/
namespace IndependentNonterminal.Linearize
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.StructuredProgram
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

variable {r s l : Nat} [NeZero l]

private def site (i : Nat) : Fin l := Fin.ofNat l i

/-- Computes the first instruction label in an interval starting at `start`.
The distinguished original global HALT label is zero. -/
def baseEntry : StructuredProgram.Cmd r s → Nat → Nat → Nat
  | .skip, _, exit => exit
  | .atom _, start, _ => start
  | .seq a b, start, exit =>
      baseEntry a start (baseEntry b (start + StructuredProgram.size a) exit)
  | .ite _ _ _, start, _ => start
  | .while _ _, start, _ => start

def callEntry : StructuredCalls.Cmd r s → Nat → Nat → Nat
  | .base b, start, exit => baseEntry b start exit
  | .call p, start, _ => start + p.entry.val
  | .seq a b, start, exit =>
      callEntry a start (callEntry b (start + StructuredCalls.size a) exit)
  | .ite _ _ _, start, _ => start
  | .while _ _, start, _ => start

/-- Static site order mirrors StructuredProgram.Site: first, second, and
ITE/WHILE guards before nested sites; all labels refer to the same global
numbering as StructuredCalls.compiled. -/
def baseCode : StructuredProgram.Cmd r s → Nat → Nat → List (Instr r s l)
  | .skip, _, _ => []
  | .atom a, _, exit => [a.instr (site exit)]
  | .seq a b, start, exit =>
      baseCode a start (baseEntry b (start + StructuredProgram.size a) exit) ++
      baseCode b (start + StructuredProgram.size a) exit
  | .ite test yes no, start, exit =>
      let ys := start + 1
      let ns := ys + StructuredProgram.size yes
      Instr.branch test (site (baseEntry yes ys exit))
        (site (baseEntry no ns exit)) ::
        (baseCode yes ys exit ++ baseCode no ns exit)
  | .while test body, start, exit =>
      Instr.branch test (site (baseEntry body (start + 1) start)) (site exit) ::
        baseCode body (start + 1) start

def callCode : StructuredCalls.Cmd r s → Nat → Nat → List (Instr r s l)
  | .base b, start, exit => baseCode b start exit
  | .call p, start, exit =>
      (List.finRange _).map (fun q =>
        ProgramLinking.relocateInstr id id (fun i => site (start + i.val))
          (some (site exit)) (p.code q))
  | .seq a b, start, exit =>
      callCode a start (callEntry b (start + StructuredCalls.size a) exit) ++
      callCode b (start + StructuredCalls.size a) exit
  | .ite test yes no, start, exit =>
      let ys := start + 1
      let ns := ys + StructuredCalls.size yes
      Instr.branch test (site (callEntry yes ys exit))
        (site (callEntry no ns exit)) ::
        (callCode yes ys exit ++ callCode no ns exit)
  | .while test body, start, exit =>
      Instr.branch test (site (callEntry body (start + 1) start)) (site exit) ::
        callCode body (start + 1) start


/-- The independent linearizer materializes one opcode per source atom/guard.
This is a GENERAL size theorem, not yet the semantic equivalence theorem. -/
theorem baseCode_length (c : StructuredProgram.Cmd r s) (start exit : Nat) :
    (baseCode (l := l) c start exit).length = StructuredProgram.size c := by
  induction c generalizing start exit with
  | skip => rfl
  | atom a => rfl
  | seq first second ih1 ih2 =>
      simp only [baseCode, List.length_append, ih1, ih2,
        StructuredProgram.size]
  | ite test yes no ih1 ih2 =>
      simp only [baseCode, List.length_cons, List.length_append,
        ih1, ih2, StructuredProgram.size]
  | «while» test body ih =>
      simp only [baseCode, List.length_cons, ih, StructuredProgram.size]

theorem callCode_length (c : StructuredCalls.Cmd r s) (start exit : Nat) :
    (callCode (l := l) c start exit).length = StructuredCalls.size c := by
  induction c generalizing start exit with
  | base b => exact baseCode_length b start exit
  | call p => simp [callCode, StructuredCalls.size]
  | seq first second ih1 ih2 =>
      simp only [callCode, List.length_append, ih1, ih2,
        StructuredCalls.size]
  | ite test yes no ih1 ih2 =>
      simp only [callCode, List.length_cons, List.length_append,
        ih1, ih2, StructuredCalls.size]
  | «while» test body ih =>
      simp only [callCode, List.length_cons, ih, StructuredCalls.size]


/-- Exactly one reserved HALT plus one site per original instruction slot. -/
def instructionArray (c : StructuredCalls.Cmd r s) : Array (Instr r s l) :=
  (Instr.halt :: callCode c 1 0).toArray


/-- Linearization never omits or adds a source instruction position. -/
theorem instructionArray_size (c : StructuredCalls.Cmd r s) :
    (instructionArray (l := l) c).size = StructuredCalls.size c + 1 := by
  simp [instructionArray, callCode_length]

end IndependentNonterminal.Linearize

namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

/-- Store the exact primitive opcode datatype in a dense array. -/
def fastArray : Array (Instr 80 1220 (StructuredCalls.size commonPrefix + 1)) :=
  Linearize.instructionArray commonPrefix

#eval (fastArray.size, StructuredCalls.size commonPrefix + 1)
#eval (fastArray[0] == program.code ⟨0,by omega⟩)
#eval (fastArray[1] == program.code program.entry)

end IndependentNonterminal
