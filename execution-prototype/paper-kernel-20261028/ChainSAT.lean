import ChainDP

namespace ChainSAT
open Polynomial

/-- The signed connected 3-CNF fixture generator used in regression_ve.py.
    Consecutive clause i uses variables (i+1),(i+2),(i+3). -/
def clauseHolds (i : Nat) (a b c : Bool) : Bool :=
  (a == ((i+1) % 3 == 0)) ||
  (b == ((i+1) % 4 == 0)) ||
  (c == ((i+1) % 5 == 0))

/-- Arithmetic weight 1 for a satisfied clause, x for one violated clause.
    The product is x^(number of violated clauses). -/
def weights {R : Type*} [Semiring R] (n : Nat) (x : R) :
    List (ChainDP.Weight R) :=
  (List.range (n-2)).map fun i a b c =>
    if clauseHolds i a b c then 1 else x

/-- Full exact polynomial computed using only four DP states at every step. -/
def satCount (n : Nat) : Nat :=
  ChainDP.fastCount (weights n (0 : Nat))

/-- Exact number of satisfying assignments of this chain 3-SAT. -/
def count (n : Nat) : Nat := satCount n

/-- The four-state algorithm equals the explicit sum-product specification. -/
theorem satCount_correct (n : Nat) :
    satCount n = ChainDP.slowCount (weights n (0 : Nat)) :=
  ChainDP.fast_eq_slow _

end ChainSAT
