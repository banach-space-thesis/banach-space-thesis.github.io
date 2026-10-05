import PFP.MatrixScalarisationSequence
import PFP.MatrixScalarisationProofs
import ThesisCommon.Analysis.BoundedProductFactorization

/-! Proposition 5.13: actual factors on the entire bounded product, obtained
from one infinite inverse branch of the finite scalarisation theorem. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem matrix_diagonal_factors_of_infinite_compressions (p : BanachExponent)
    (D : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p)
    (F : ∀ n, MatrixBlock 𝕜 p (n+1) →L[𝕜] MatrixBlock 𝕜 p (n+1))
    (hD : ∀ x n, D x n = F n (x n))
    (m : ℕ → ℕ) (hm : StrictMono m)
    (α τ : ∀ n, Fin (n+1) ↪o Fin (m n+1))
    (S : Set ℕ) (hS : S.Infinite)
    (h : ∀ n ∈ S, HasMatrixInverseBound 𝕜 p (n+1)
      (((matrixRestrict (𝕜 := 𝕜) p (α n).toEmbedding (τ n).toEmbedding).comp (F (m n))).comp
        (matrixInsert (𝕜 := 𝕜) p (α n).toEmbedding (τ n).toEmbedding)) 4) :
    ∃ U V : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p,
      (U.comp D).comp V = ContinuousLinearMap.id 𝕜 _ ∧ ‖U‖ * ‖V‖ ≤ 4 := by
  classical
  obtain ⟨a, ha, haS⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨n, hnS, hn⟩ := hS.exists_notMem_finset (Finset.range (N+1))
    exact ⟨n, Nat.lt_of_succ_le (by simpa only [Finset.mem_range, not_lt] using hn), hnS⟩)
  choose R hR hRright hnR using fun i => h (a i) (haS i)
  let e (i : ℕ) : Fin (i+1) ↪ Fin (a i+1) :=
    Fin.castLEEmb (Nat.add_le_add_right (ha.id_le i) 1)
  let J (i : ℕ) := matrixInsert (𝕜 := 𝕜) p (α (a i)).toEmbedding (τ (a i)).toEmbedding
  let K (i : ℕ) := matrixRestrict (𝕜 := 𝕜) p (α (a i)).toEmbedding (τ (a i)).toEmbedding
  let L (i : ℕ) := matrixInsert (𝕜 := 𝕜) p (e i) (e i)
  let P (i : ℕ) := matrixRestrict (𝕜 := 𝕜) p (e i) (e i)
  have hJ (i : ℕ) : ‖J i‖ ≤ 1 := norm_matrixInsert_le p _ _
  have hK (i : ℕ) : ‖K i‖ ≤ 1 := norm_matrixRestrict_le p _ _
  have hL (i : ℕ) : ‖L i‖ ≤ 1 := norm_matrixInsert_le p _ _
  have hP (i : ℕ) : ‖P i‖ ≤ 1 := norm_matrixRestrict_le p _ _
  have hr (i : ℕ) : ‖(J i).comp (L i)‖ ≤ 1 := by
    apply ((J i).opNorm_comp_le (L i)).trans
    simpa only [one_mul] using mul_le_mul (hJ i) (hL i) (L i).opNorm_nonneg zero_le_one
  have hs (i : ℕ) : ‖(P i).comp ((R i).comp (K i))‖ ≤ 4 := by
    have hRK : ‖(R i).comp (K i)‖ ≤ 4 := by
      apply ((R i).opNorm_comp_le (K i)).trans
      simpa only [mul_one] using mul_le_mul (hnR i) (hK i) (K i).opNorm_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    apply ((P i).opNorm_comp_le ((R i).comp (K i))).trans
    simpa only [one_mul] using mul_le_mul (hP i) hRK ((R i).comp (K i)).opNorm_nonneg zero_le_one
  apply boundedProduct_factorization_of_coordinate_factors D (m ∘ a) (hm.comp ha).injective
    (fun i => F (m (a i))) (fun x i => hD x (m (a i)))
    (fun i => (J i).comp (L i)) hr
    (fun i => (P i).comp ((R i).comp (K i))) 4 (by norm_num) hs
  intro i
  apply ContinuousLinearMap.ext
  intro x
  have hi := DFunLike.congr_fun (hR i) (L i x)
  change R i (K i (F (m (a i)) (J i (L i x)))) = L i x at hi
  change P i (R i (K i (F (m (a i)) (J i (L i x))))) = x
  rw [hi]
  exact DFunLike.congr_fun (matrixRestrict_comp_insert (𝕜 := 𝕜) p (e i) (e i)) x

theorem matrix_diagonal_dichotomy (p : BanachExponent) (hp : 1 < p.val.toReal)
    (D : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p) (hD : IsMatrixSumDiagonal p D) :
    ∃ U V : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p,
      ((U.comp D).comp V = ContinuousLinearMap.id 𝕜 _ ∨
        (U.comp (ContinuousLinearMap.id 𝕜 _ - D)).comp V = ContinuousLinearMap.id 𝕜 _) ∧
      ‖U‖ * ‖V‖ ≤ 4 := by
  classical
  obtain ⟨F, hD⟩ := hD
  obtain ⟨m, hm, _, hselect⟩ := exists_matrix_scalarisation_sequence p
    (finiteMatrixScalarisation 𝕜 p hp) D F hD
  choose α τ hchoice using hselect
  let S : Set ℕ := {n | HasMatrixInverseBound 𝕜 p (n+1)
    (((matrixRestrict (𝕜 := 𝕜) p (α n).toEmbedding (τ n).toEmbedding).comp (F (m n))).comp
      (matrixInsert (𝕜 := 𝕜) p (α n).toEmbedding (τ n).toEmbedding)) 4}
  by_cases hS : S.Infinite
  · obtain ⟨U, V, heq, hn⟩ := matrix_diagonal_factors_of_infinite_compressions p D F hD
      m hm α τ S hS (fun _ hn => hn)
    exact ⟨U, V, Or.inl heq, hn⟩
  · have hc : Sᶜ.Infinite := (Set.not_infinite.mp hS).infinite_compl
    have hcomp : ∀ (x : MatrixSum 𝕜 p) n,
        (ContinuousLinearMap.id 𝕜 (MatrixSum 𝕜 p) - D) x n =
          (ContinuousLinearMap.id 𝕜 (MatrixBlock 𝕜 p (n+1)) - F n) (x n) := by
      intro x n
      change x n - D x n = x n - F n (x n)
      rw [hD]
    obtain ⟨U, V, heq, hn⟩ := matrix_diagonal_factors_of_infinite_compressions p
      (ContinuousLinearMap.id 𝕜 _ - D) (fun n => ContinuousLinearMap.id 𝕜 _ - F n)
      hcomp m hm α τ Sᶜ hc (fun n hn => (hchoice n).resolve_left hn)
    exact ⟨U, V, Or.inr heq, hn⟩

theorem proposition_5_13 : Proposition_5_13 𝕜 := by
  intro p hp hfin D hD
  apply matrix_diagonal_dichotomy p _ D hD
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp

end PFP
