import OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction

namespace ExperimentalCRT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def ops7 : SubexpSymbolicCost.RingProgram (ZMod 7) where
  zeroRun := (0,1)
  oneRun := (1,1)
  addRun := fun a b => (a+b,1)
  mulRun := fun a b => (a*b,1)
  negRun := fun a => (-a,1)

private def nodes7 : Fin 2 → ZMod 7 := fun i => i.val
private def jets7 : Fin 2 → List (ZMod 7) := fun i => [(3:ZMod 7)+2*(i.val:ZMod 7)]
private def result7 := Reconstruction.run ops7 nodes7 7 1 1 jets7

#eval result7.1.map ZMod.val
#eval result7.2
#eval decide (result7.1.take 2 = ([3,2]:List (ZMod 7)))

namespace MoreNodes
private def coeffs : List (ZMod 7) := [3,2,1,4,5]
private def evalAt (x : ZMod 7) : ZMod 7 :=
  coeffs.reverse.foldl (fun acc c => acc*x+c) 0
private def nodes : Fin 5 → ZMod 7 := fun i => i.val
private def jets : Fin 5 → List (ZMod 7) := fun i => [evalAt (nodes i)]
private def recon := Reconstruction.run ops7 nodes 7 1 1 jets
#eval recon.1.take 5 |>.map ZMod.val
#eval recon.2
#eval decide ((recon.1.take 5) = coeffs)
end MoreNodes
end ExperimentalCRT
