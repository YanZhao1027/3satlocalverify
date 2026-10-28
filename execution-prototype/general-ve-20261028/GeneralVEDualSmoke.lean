import GeneralVEWeighted
import ConnectedCRT
import HermiteKernel

private def F8 := ConnectedCRT.F

#eval (GeneralVEWeighted.dualJet F8 (0 : ZMod 7)).fst.val
#eval (GeneralVEWeighted.dualJet F8 (0 : ZMod 7)).snd.val
#eval (GeneralVEWeighted.dualJet F8 (1 : ZMod 7)).fst.val
#eval (GeneralVEWeighted.dualJet F8 (1 : ZMod 7)).snd.val
#eval (GeneralVEWeighted.dualJet F8 (2 : ZMod 7)).fst.val
#eval (GeneralVEWeighted.dualJet F8 (2 : ZMod 7)).snd.val

private def jets : Fin 3 → List (ZMod 7) := fun i =>
  let r := GeneralVEWeighted.dualJet F8 i.val
  [r.fst,r.snd]

private def reconstruct :=
  OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction.run
    (PaperKernel.ops 7) (fun i : Fin 3 => (i.val: ZMod 7)) 7 1 2 jets

#eval (reconstruct.1.take 6).map ZMod.val
#eval reconstruct.2
#eval ((reconstruct.1.take 6).map ZMod.val == [4,1,6,0,0,0])
