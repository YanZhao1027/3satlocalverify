import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAlgorithm

open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def ops : MomentsAlgorithm.Ops Nat (Fin 2) Nat where
  zero := 0
  one := 1
  add := fun a b => (a + b, 1)
  mul := fun a b => (a * b, 1)
  scale := fun r a => (r * a, 1)
  project := fun i a => ((i.val + 1) * a, 1)

private def buckets (i : Fin 2) : List (List (Nat × Nat)) :=
  if i == 0 then [[(2, 3), (4, 5)], [(3, 2)]]
  else [[(1, 7), (3, 2)], [(4, 2)]]

#eval MomentsAlgorithm.run ops buckets [0, 1]
example : MomentsAlgorithm.run ops buckets [0, 1] = (364, 20) := by decide
