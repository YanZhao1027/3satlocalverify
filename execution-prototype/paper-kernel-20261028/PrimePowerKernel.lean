import HermiteKernel

namespace PaperKernel
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Non-field prime-power residue ring ZMod (7^2), carrying the original
    nilpotent-correction inverse algorithm with residue cardinality q=7, μ=2. -/
def reconstructPrimePower (coeffs : List Nat) (Q D : Nat) :
    List (ZMod 49) × Nat :=
  Reconstruction.run (ops 49) (fun i : Fin Q => (i.val : ZMod 49)) 7 2 D
    (fun i : Fin Q => taylorJets 49 coeffs i.val D)

/-- Ordinary integer CRT coefficients for coprime moduli 49,11,13.
    Product 7007 > 2^11, the maximum number of satisfying assignments in demo. -/
def recover49_11_13 (c49 c11 c13 : Nat) : Nat :=
  (c49 * 1716 + c11 * 6370 + c13 * 5929) % 7007

end PaperKernel
