import Posets.CZeroMatrixOperators

noncomputable section
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [Nonempty P]

theorem operator_apply_scalarMatrix (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P)
    (x : CZeroOn 𝕜 P) (s : P) : T x ⟨s⟩ = ∑' t, scalarMatrix 𝕜 T s t * x ⟨t⟩ := by
  have heq : cZeroMatrixOperator (scalarMatrix 𝕜 T)
      (scalarMatrix_boundedRows T) (scalarMatrix_zeroColumns T) = T :=
    scalarMatrix_injective (scalarMatrix_cZeroMatrixOperator _ _ _)
  exact (congrArg (fun U : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P => U x ⟨s⟩) heq).symm

theorem scalarMatrix_mul (S T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) (s t : P) :
    scalarMatrix 𝕜 (S * T) s t = ∑' r, scalarMatrix 𝕜 S s r * scalarMatrix 𝕜 T r t :=
  operator_apply_scalarMatrix S (T (unitVector 𝕜 t)) s

omit [Nonempty P] in
theorem scalarMatrix_mul_summable (S T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) (s t : P) :
    Summable (fun r => scalarMatrix 𝕜 S s r * scalarMatrix 𝕜 T r t) :=
  cZeroMatrix_summable _ (scalarMatrix_boundedRows S) (T (unitVector 𝕜 t)) s

end Posets
