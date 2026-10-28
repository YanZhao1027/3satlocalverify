import ConnectedCRT
import CRTKernel

namespace HermiteCRT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def hist : List Nat := (List.range 6).map ConnectedCRT.histogram
private def deriv : List Nat := (List.range 5).map fun j => (j+1) * (hist.getD (j+1) 0)

/-- Order-2 Taylor jets: value and first derivative at each node.
    3 nodes * 2 jet coefficients = 6 degrees of freedom. -/
def run (p : Nat) : List (ZMod p) × Nat :=
  Reconstruction.run (PaperKernel.ops p) (fun i : Fin 3 => (i.val:ZMod p)) p 1 2
    (fun i : Fin 3 =>
      [PaperKernel.evalPolynomial p hist (i.val:ZMod p),
       PaperKernel.evalPolynomial p deriv (i.val:ZMod p)])

#eval hist
#eval deriv
#eval (run 7).1.take 6 |>.map ZMod.val
#eval (run 11).1.take 6 |>.map ZMod.val
#eval (run 13).1.take 6 |>.map ZMod.val
#eval (run 7).2
#eval (run 11).2
#eval (run 13).2
#eval ((run 7).1.take 6).map ZMod.val == hist.map (· % 7)
#eval ((run 11).1.take 6).map ZMod.val == hist.map (· % 11)
#eval ((run 13).1.take 6).map ZMod.val == hist.map (· % 13)

end HermiteCRT

namespace HermiteHigher
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def hist := (List.range 6).map ConnectedCRT.histogram
private def jetTaylor (p : Nat) (x : ZMod p) (order : Nat) : List (ZMod p) :=
  (List.range order).map fun k =>
    (List.range 6).foldl (fun acc j =>
      acc + ((Nat.choose j k * hist.getD j 0 : Nat) : ZMod p) * x^(j-k)) 0

def run3 (p : Nat) : List (ZMod p) × Nat :=
  Reconstruction.run (PaperKernel.ops p) (fun i : Fin 2 => (i.val : ZMod p)) p 1 3
    (fun i => jetTaylor p i.val 3)

#eval (run3 7).1.take 6 |>.map ZMod.val
#eval (run3 11).1.take 6 |>.map ZMod.val
#eval (run3 13).1.take 6 |>.map ZMod.val
#eval (run3 7).2
#eval (run3 11).2
#eval (run3 13).2
#eval ((run3 7).1.take 6).map ZMod.val == hist.map (· % 7)
#eval ((run3 11).1.take 6).map ZMod.val == hist.map (· % 11)
#eval ((run3 13).1.take 6).map ZMod.val == hist.map (· % 13)
end HermiteHigher
