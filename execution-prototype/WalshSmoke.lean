import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence

open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def candidate := WalshExistence.search 2 4 2

#eval candidate.isSome
#eval candidate.map fun s => (List.finRange 4).map fun i => (List.finRange 2).map fun j => (s i j).val
#eval candidate.map fun s => decide (WalshExistence.Good 2 s)
#eval candidate.map fun s =>
  (List.finRange 2).flatMap fun i =>
    (List.finRange 2).map fun j =>
      WalshExistence.walshInt s ![i, j]

private def balanced := WalshExistence.search 2 4 3
#eval balanced.isSome
#eval balanced.map fun s => (List.finRange 4).map fun i => (List.finRange 2).map fun j => (s i j).val
#eval balanced.map fun s => decide (WalshExistence.Good 3 s)
#eval balanced.map fun s =>
  (List.finRange 2).flatMap fun i =>
    (List.finRange 2).map fun j =>
      WalshExistence.walshInt s ![i, j]

private theorem search_is_sound (s) (h : WalshExistence.search 2 4 3 = some s) :
    WalshExistence.Good 3 s := WalshExistence.search_some_good h
