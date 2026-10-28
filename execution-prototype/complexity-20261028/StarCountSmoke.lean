import PermutationCorrect

/-! 3-CNF with one hub literal appearing in each clause. The hypergraph is
    connected, but reversing the variable order avoids catastrophic fill-in.
    This calls the actual, verified memoized factor elimination implementation. -/
namespace StarCountSmoke
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

private def lit (n : Nat) [NeZero n] (i : Nat) : Literal (Fin n) :=
  ⟨Fin.ofNat n i, true⟩

def starCNF (n : Nat) [NeZero n] : CNF (Fin n) :=
  ((List.range (n-2)).map (fun i =>
    ([lit n 0, lit n (i+1), lit n (i+2)] : List (Literal (Fin n))).toFinset)).toFinset

def reverseCount (n : Nat) [NeZero n] : Nat :=
  GeneralVESAT.exactCountWithOrder (starCNF n) (List.finRange n).reverse

/-- Changing to reverse elimination does not change the resulting exact #SAT,
    even though it radically reduces support width for these inputs. -/
theorem reverseCount_correct (n : Nat) [NeZero n] :
    reverseCount n = SAT.count (starCNF n) := by
  exact GeneralVESAT.exactCountWithOrder_correct (starCNF n)
    (List.finRange n).reverse (List.reverse_perm _)

#eval reverseCount 16
#eval reverseCount 32
#eval reverseCount 64

end StarCountSmoke
