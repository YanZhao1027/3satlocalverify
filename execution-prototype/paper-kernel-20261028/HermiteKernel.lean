import CRTKernel

namespace PaperKernel
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- The kth coefficient of P(X+a) is the ordinary k-th Hasse derivative
    at a, computed by the binomial identity. No factorial inverses needed. -/
def taylorJets (p : Nat) (coeffs : List Nat)
    (a : ZMod p) (order : Nat) : List (ZMod p) :=
  (List.range order).map fun k =>
    (List.range coeffs.length).foldl (fun acc j =>
      acc + ((Nat.choose j k * coeffs.getD j 0 : Nat) : ZMod p) * a^(j-k)) 0

/-- Original paper Reconstruction.run on Hermite jets: Q sites of order D.
    Q*D=6 is selected by the CLI (6x1, 3x2 or 2x3). -/
def reconstructHermite (p : Nat) (coeffs : List Nat) (Q D : Nat) :
    List (ZMod p) × Nat :=
  Reconstruction.run (ops p) (fun i : Fin Q => (i.val : ZMod p)) p 1 D
    (fun i : Fin Q => taylorJets p coeffs i.val D)

end PaperKernel
