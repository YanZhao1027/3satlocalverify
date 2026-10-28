import HermiteKernel
import ConnectedCRT

namespace PrimePowerCRT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def hist : List Nat := (List.range 6).map ConnectedCRT.histogram

/-- This is not a field: ZMod (7^2) has nilpotents. The original paper's
    residue-power inverse routine uses q=7, μ=2, and handles division by units
    with the full nilpotent correction factor. -/
def run (Q D : Nat) : List (ZMod 49) × Nat :=
  Reconstruction.run (PaperKernel.ops 49) (fun i : Fin Q => (i.val:ZMod 49)) 7 2 D
    (fun i : Fin Q => PaperKernel.taylorJets 49 hist i.val D)

#eval (run 6 1).1.take 6 |>.map ZMod.val
#eval (run 3 2).1.take 6 |>.map ZMod.val
#eval (run 2 3).1.take 6 |>.map ZMod.val
#eval (run 6 1).2
#eval (run 3 2).2
#eval (run 2 3).2
#eval ((run 6 1).1.take 6).map ZMod.val == hist.map (· % 49)
#eval ((run 3 2).1.take 6).map ZMod.val == hist.map (· % 49)
#eval ((run 2 3).1.take 6).map ZMod.val == hist.map (· % 49)

end PrimePowerCRT
