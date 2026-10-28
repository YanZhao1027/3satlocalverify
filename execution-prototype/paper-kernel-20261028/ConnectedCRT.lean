import OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction
import MomentsSAT

namespace ConnectedCRT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SAT

private def lit (v : Fin 8) (pol : Bool) : Literal (Fin 8) := ⟨v,pol⟩
private def c (ls : List (Literal (Fin 8))) : Clause (Fin 8) := ls.toFinset

/-- A genuinely connected, nontrivial 3-CNF with all 8 variables used. -/
def clauses : List (Clause (Fin 8)) :=
  [c [lit 0 true, lit 1 true, lit 2 true],
   c [lit 1 false, lit 3 true, lit 4 true],
   c [lit 3 false, lit 5 true, lit 6 true],
   c [lit 0 true, lit 6 false, lit 7 true],
   c [lit 2 false, lit 4 false, lit 7 false]]

def F : CNF (Fin 8) := clauses.toFinset

/-- A coefficient of the SAT violation polynomial is the number of
    assignments violating exactly j clauses; the constant term is #SAT. -/
def violations (a : Assignment (Fin 8)) : Nat :=
  (clauses.filter (fun C => !(C.eval a))).length

def histogram (j : Nat) : Nat :=
  ((Prototype.assignments 8).filter (fun a => violations a == j)).length

/-- Evaluate the full polynomial at a point over a finite modular ring. -/
def polyEval (p : Nat) (x : ZMod p) : ZMod p :=
  (List.range 6).reverse.foldl (fun acc j => acc*x + (histogram j : ZMod p)) 0

/-- The real source reconstruction algorithm with explicit field operations
    and an auditable count of its scalar arithmetic callbacks. -/
def ringOps (p : Nat) : SubexpSymbolicCost.RingProgram (ZMod p) where
  zeroRun := (0,1)
  oneRun := (1,1)
  addRun := fun a b => (a+b,1)
  mulRun := fun a b => (a*b,1)
  negRun := fun a => (-a,1)

def nodes (p : Nat) : Fin 6 → ZMod p := fun i => i.val

def jets (p : Nat) : Fin 6 → List (ZMod p) :=
  fun i => [polyEval p (nodes p i)]

def result (p : Nat) : List (ZMod p) × Nat :=
  Reconstruction.run (ringOps p) (nodes p) p 1 1 (jets p)

#eval (List.range 6).map histogram
#eval SAT.count F
#eval (result 7).1.take 6 |>.map ZMod.val
#eval (result 11).1.take 6 |>.map ZMod.val
#eval (result 13).1.take 6 |>.map ZMod.val
#eval (result 7).2
#eval (result 11).2
#eval (result 13).2
#eval (((result 7).1.take 6).map ZMod.val == (List.range 6).map (fun j => histogram j % 7))
#eval (((result 11).1.take 6).map ZMod.val == (List.range 6).map (fun j => histogram j % 11))
#eval (((result 13).1.take 6).map ZMod.val == (List.range 6).map (fun j => histogram j % 13))


/-- Ordinary integer CRT combines the modular constant coefficients.
    7*11*13=1001 exceeds 2^8, the maximum number of satisfying assignments. -/
def reconstructedSAT : Nat :=
  (((result 7).1.headD 0).val * 715 +
   ((result 11).1.headD 0).val * 364 +
   ((result 13).1.headD 0).val * 924) % 1001

#eval reconstructedSAT
#eval decide (reconstructedSAT = SAT.count F)

/-- Apply the original Walsh character evaluation to the actual set of
    satisfying Boolean assignments, rather than a synthetic Walsh sample. -/
def asCube (a : Assignment (Fin 8)) : Cayley.Cube 8 :=
  fun j => if a j then 1 else 0

def satWalsh (mask : Cayley.Cube 8) : Int :=
  (Prototype.assignments 8).foldl
    (fun acc a => acc + (if F.eval a then
      WalshExistence.characterInt mask (asCube a) else 0)) 0

def unitMask (j : Fin 8) : Cayley.Cube 8 :=
  fun i => if i == j then 1 else 0

#eval satWalsh 0
#eval (List.finRange 8).map (fun j => satWalsh (unitMask j))
#eval decide (satWalsh 0 = (SAT.count F : Int))

end ConnectedCRT
