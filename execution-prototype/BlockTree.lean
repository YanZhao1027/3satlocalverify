import BlockProduct

namespace Prototype.BlockTree
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

/-- A syntactically certified tree of variable-disjoint subproblems. -/
inductive Tree : Nat → Type
  | leaf {n : Nat} (F : CNF (Fin n)) : Tree n
  | node {n m : Nat} (left : Tree n) (right : Tree m) : Tree (n + m)

/-- The exact CNF represented by a tree, with disjoint coordinate ranges. -/
def toCNF : {n : Nat} → Tree n → CNF (Fin n)
  | _, .leaf F => F
  | _, .node l r => BlockProduct.joined (toCNF l) (toCNF r)

/-- Compute only each bounded leaf's active assignments; multiply independent counts. -/
def count : {n : Nat} → Tree n → Nat
  | _, .leaf F => Prototype.countActive F
  | _, .node l r => count l * count r

/-- A kernel-checked exact #SAT theorem for the whole recursively-composed CNF. -/
theorem correct {n : Nat} (t : Tree n) : count t = SAT.count (toCNF t) := by
  induction t with
  | leaf F => exact Prototype.countActive_correct F
  | node l r ihl ihr =>
      simp only [count, toCNF, BlockProduct.count_joined]
      rw [ihl, ihr]

/-- All six pairwise-positive 2-SAT clauses on the same four variables. -/
def pairs4 : CNF (Fin 4) :=
  let lit (i : Fin 4) : Literal (Fin 4) := ⟨i,true⟩
  ([{lit 0,lit 1}, {lit 0,lit 2}, {lit 0,lit 3},
    {lit 1,lit 2}, {lit 1,lit 3}, {lit 2,lit 3}] :
    List (Clause (Fin 4))).toFinset

/-- Each four-variable group has exactly five satisfying assignments. -/
theorem pairs4_count : Prototype.countActive pairs4 = 5 := by decide

/-- k disjoint four-variable groups: k*4 actual active variables. -/
def groups : (k : Nat) → Tree (4 * k)
  | 0 => .leaf (∅ : CNF (Fin 0))
  | k + 1 => .node (groups k) (.leaf pairs4)

/-- Source-level cost is k exact support counts of 2^4 each, versus 2^(4*k)
    ambient enumeration. The precise algorithmic complexity excludes formula
    construction/encoding, and this special structure does not imply generic ETH. -/
theorem groups_count (k : Nat) : count (groups k) = 5 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [groups, count, ih, pairs4_count, pow_succ]

end Prototype.BlockTree
