import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets

/-! Independently checked bridge from the original executable native leaf
command contract to its formally established paper-scale time envelope. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract

open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

theorem uniform_contract_and_runtimeBound
    (k K g Pc Pd : ℕ) (hk : 2 ≤ k) :
    ∃ Cs sd : ℕ, ∃ Ct At : ℝ, ∃ td cutoff : ℕ,
      ∃ D : ℝ, ∃ e : ℕ,
        1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ td ∧ 1 ≤ D ∧
        ∀ n L parameterBound bound : ℕ,
          cutoff ≤ n →
          n ≤ L →
          parameterBound ≤ Pc * (L + 1) ^ Pd →
          ∀ threshold : List Bool,
            BinaryArithmetic.toNat threshold =
              SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) →
            Cs * (L + 1) ^ sd ≤ bound →
            101 * SparseCountProgram.formulaBound n k + 103 ≤ bound →
            5 * n + 6 ≤ bound →
            bound ≤ K * (L + 1) ^ g →
            (LeafContract (n := n) k threshold parameterBound
              (NativeLeafProgram.command k)
              (NativeLeafContract.time n k
                (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At td L n))
                bound)
              bound) ∧
            ((NativeLeafContract.time n k
                (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At td L n))
                bound : ℕ) : ℝ) ≤
              SqrtLog.Statement.runtimeBound D At e L n := by
  obtain ⟨Cs, sd, Ct, At, td, cutoff, hCt, hAt, htd, hcontract⟩ :=
    NativeLeafContract.uniform_contract k Pc Pd hk
  have hAt0 : (0 : ℝ) ≤ At := le_trans zero_le_one hAt
  obtain ⟨D, e, hD, henvelope⟩ :=
    NativeOuterBudgets.leafTime_runtimeBound k K g Ct At hCt hAt0 td
  refine ⟨Cs, sd, Ct, At, td, cutoff, D, e, hCt, hAt, htd, hD, ?_⟩
  intro n L parameterBound bound hcut hnL hp threshold hthreshold
    hspace hclassifier hpower hupper
  constructor
  · exact hcontract n L parameterBound bound hcut hnL hp threshold
      hthreshold hspace hclassifier hpower
  · simpa only [NativeLeafContract.time] using
      (henvelope n L bound hnL hupper)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
