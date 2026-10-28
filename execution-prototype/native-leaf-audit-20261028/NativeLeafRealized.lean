import NativeLeafCostBridge
import NativeLeafBudgetFeasible

/-! Coordinator-checked strengthening of two Sol-proposed proofs: rather than
assuming a possibly contradictory upper bound K for the native leaf stack,
construct a single polynomial bound that meets all THREE required lower
bounds uniformly, before choosing the paper-scale runtime envelope. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract

open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

/-- For EVERY sufficiently large input under the original parameter
conditions, there is a CONSTRUCTIVE globally budgeted native leaf contract
and a corresponding paper-scale runtime envelope. The global constants
are chosen before n/L/threshold; there is no arbitrary unknown upper K.
This is ONLY a native-leaf subprogram theorem, not a complete SAT solver. -/
theorem uniform_leaf_with_constructed_budget
    (k Pc Pd : ℕ) (hk : 2 ≤ k) :
    ∃ Cs sd : ℕ, ∃ Ct At : ℝ, ∃ td cutoff : ℕ,
      ∃ D : ℝ, ∃ e : ℕ,
      1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ td ∧ 1 ≤ D ∧
      ∀ n L parameterBound : ℕ, cutoff ≤ n → n ≤ L →
        parameterBound ≤ Pc * (L + 1) ^ Pd →
        ∀ threshold : List Bool,
          BinaryArithmetic.toNat threshold =
            SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) →
          LeafContract (n := n) k threshold parameterBound
            (NativeLeafProgram.command k)
            (time n k (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At td L n))
              (nativeLeafFeasibleBudget k Cs sd n L))
            (nativeLeafFeasibleBudget k Cs sd n L) ∧
          ((time n k (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At td L n))
              (nativeLeafFeasibleBudget k Cs sd n L) : ℕ) : ℝ) ≤
            SqrtLog.Statement.runtimeBound D At e L n := by
  obtain ⟨Cs, sd, Ct, At, td, cutoff, hCt, hAt, htd, hcontract⟩ :=
    uniform_contract k Pc Pd hk
  let c : ℕ := 2 + (4 + 8 * k) * (k + 1) * 2 ^ k
  let g : ℕ := max sd (k + 1)
  let K : ℕ := Cs + 101 * c + 114
  obtain ⟨D, e, hD, henvelope⟩ :=
    NativeOuterBudgets.leafTime_runtimeBound k K g Ct At hCt (by linarith) td
  refine ⟨Cs, sd, Ct, At, td, cutoff, D, e, hCt, hAt, htd, hD, ?_⟩
  intro n L parameterBound hcut hn hparam threshold hthreshold
  have hbudget := nativeLeaf_polynomialBudget_feasible k Cs sd n L hn
  dsimp only at hbudget
  obtain ⟨hspace, hclassifier, hpower, hupper⟩ := hbudget
  let bound := nativeLeafFeasibleBudget k Cs sd n L
  constructor
  · exact hcontract n L parameterBound bound hcut hn hparam threshold
      hthreshold hspace hclassifier hpower
  · simpa only [NativeLeafContract.time] using
      (henvelope n L bound hn hupper)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
