import DimacsCore
import MomentsSAT
import OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction

namespace PaperKernel
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SAT

/-- The SAT-derived violation polynomial: coefficient j counts assignments
    falsifying exactly j clauses, including all ambient free variables. -/
def countViolations {n : Nat} (cs : List (Clause (Fin n)))
    (a : Assignment (Fin n)) : Nat :=
  (cs.filter (fun C => !(C.eval a))).length

def coefficient {n : Nat} (cs : List (Clause (Fin n))) (j : Nat) : Nat :=
  ((Prototype.assignments n).filter (fun a => decide (countViolations cs a = j))).length

def polynomialCoefficients {n : Nat} (cs : List (Clause (Fin n))) : List Nat :=
  (List.range 6).map (coefficient cs)

/-- Fully executable coefficient operations fed into the original paper's
    Reconstruction.run; q in {7,11,13} and Q=6, order 1 in this demo. -/
def ops (p : Nat) : SubexpSymbolicCost.RingProgram (ZMod p) where
  zeroRun := (0,1)
  oneRun := (1,1)
  addRun := fun a b => (a+b,1)
  mulRun := fun a b => (a*b,1)
  negRun := fun a => (-a,1)

def evalPolynomial (p : Nat) (coeffs : List Nat) (x : ZMod p) : ZMod p :=
  coeffs.reverse.foldl (fun acc c => acc*x+(c:ZMod p)) 0

def reconstruct (p : Nat) (coeffs : List Nat) : List (ZMod p) × Nat :=
  Reconstruction.run (ops p) (fun i : Fin 6 => (i.val:ZMod p)) p 1 1
    (fun i : Fin 6 => [evalPolynomial p coeffs (i.val:ZMod p)])

/-- Elementary integer CRT: coefficients 715/364/924 are inverses for
    moduli 7/11/13 respectively. The product 1001 > 2^9 (input cap). -/
def exactCRT (coeffs : List Nat) : Nat :=
  let a := ((reconstruct 7 coeffs).1.headD 0).val
  let b := ((reconstruct 11 coeffs).1.headD 0).val
  let c := ((reconstruct 13 coeffs).1.headD 0).val
  (a*715+b*364+c*924)%1001

/-- Actual Walsh character routine in the original source, applied to
    satisfying assignments of the input formula. -/
def asCube {n : Nat} (a : Assignment (Fin n)) : Cayley.Cube n :=
  fun j => if a j then 1 else 0

def walshCoefficient {n : Nat} (F : CNF (Fin n)) (mask : Cayley.Cube n) : Int :=
  (Prototype.assignments n).foldl
    (fun sum a => sum + (if F.eval a then
      WalshExistence.characterInt mask (asCube a) else 0)) 0

def unitMask {n : Nat} (i : Fin n) : Cayley.Cube n :=
  fun j => if j == i then 1 else 0

end PaperKernel
