import GeneralVESAT
import ConnectedCRT

open OAI.Algorithms.SubexponentialSAT

private def f8 := ConnectedCRT.F

#eval GeneralVE.product (GeneralVESAT.runFactors f8) (fun _ => false)
#eval SAT.count f8

private def l11 (v : Fin 11) (p : Bool) : SAT.Literal (Fin 11) := ⟨v,p⟩
private def c11 (ls : List (SAT.Literal (Fin 11))) : SAT.Clause (Fin 11) := ls.toFinset
private def F11 : SAT.CNF (Fin 11) :=
  ([c11 [l11 0 true,l11 1 true,l11 2 true],
    c11 [l11 2 false,l11 3 true,l11 4 true],
    c11 [l11 4 false,l11 5 true,l11 6 true],
    c11 [l11 6 false,l11 7 true,l11 8 true],
    c11 [l11 8 false,l11 9 true,l11 10 true]] : List (SAT.Clause (Fin 11))).toFinset

#eval GeneralVE.product (GeneralVESAT.runFactors F11) (fun _ => false)
#eval SAT.count F11
