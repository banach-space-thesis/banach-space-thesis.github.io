import PL1.DecompositionRNP
import Mathlib.Analysis.RCLike.Lemmas

/-! # Scalar restriction for finite-dimensional projection decompositions -/

noncomputable section
universe u v
open Filter
open scoped Topology

namespace PL1.ScalarDecompositionRNP

variable {K : Type*} [RCLike K]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]

/-- Bounded completeness expressed directly for scalar-linear projections and the inherited norm. -/
def BoundedlyComplete (P : ℕ → E →L[K] E) : Prop :=
  ∀ x : ℕ → E, (∀ m n, m ≤ n → P m (x n) = x m) →
    (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) → ∃ a, Tendsto x atTop (𝓝 a)

/-- Scalar-linear boundedly complete finite-dimensional projections give the full RNP
of the underlying real space, with exactly the inherited norm. -/
theorem hasRNP_of_scalar_projections
    (P : ℕ → E →L[K] E) (hfinite : ∀ n, FiniteDimensional K (P n).range)
    (hnested : ∀ m n, m ≤ n → (P m).comp (P n) = P m)
    (hbound : ∃ C : ℝ, ∀ n, ‖P n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hBC : ∀ x : ℕ → E, (∀ m n, m ≤ n → P m (x n) = x m) →
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) → ∃ a, Tendsto x atTop (𝓝 a)) :
    @HasRadonNikodymProperty.{u, v} (UnderlyingReal K E)
      (inferInstanceAs (NormedAddCommGroup E)) (NormedSpace.restrictScalars ℝ K E) := by
  let := NormedSpace.restrictScalars ℝ K E
  let := IsScalarTower.restrictScalars ℝ K E
  change HasRadonNikodymProperty.{u, v} E
  let Q : ℕ → E →L[ℝ] E := fun n => (P n).restrictScalars ℝ
  have hfiniteR (n : ℕ) : FiniteDimensional ℝ (Q n).range := by
    let := hfinite n
    let : FiniteDimensional ℝ (P n).range := FiniteDimensional.trans ℝ K (P n).range
    exact inferInstanceAs (FiniteDimensional ℝ (P n).range)
  apply DecompositionRNP.hasRadonNikodymProperty_of_boundedlyCompleteDecomposition
  refine {
    projection := Q
    finiteDimensional := hfiniteR
    nested := ?_
    uniformBound := ?_
    tendsto_identity := hstrong
    bounded_complete := hBC }
  · intro m n hmn
    ext1 x
    exact DFunLike.congr_fun (hnested m n hmn) x
  · obtain ⟨C, hC⟩ := hbound
    exact ⟨C, fun n => (ContinuousLinearMap.norm_restrictScalars (P n)).trans_le (hC n)⟩

/-- A failed bounded-completeness condition supplies a bounded coherent branch which is not Cauchy. -/
theorem exists_nonCauchy_branch (P : ℕ → E →L[K] E) (hP : ¬ BoundedlyComplete P) :
    ∃ x : ℕ → E, (∀ m n, m ≤ n → P m (x n) = x m) ∧
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) ∧ ¬ CauchySeq x := by
  classical
  by_contra! h
  apply hP
  intro x hx hbounded
  exact cauchySeq_tendsto_of_complete (h x hx hbounded)

end PL1.ScalarDecompositionRNP
