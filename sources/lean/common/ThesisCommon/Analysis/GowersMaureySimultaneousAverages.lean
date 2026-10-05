import ThesisCommon.Analysis.GowersMaureyNormingFamilies
import ThesisCommon.Analysis.GowersMaureyBlockAverageDetection

/-! Actual simultaneous bad averages for finitely many operators. A single
genuine continuous functional detects every average, has norm at most two,
and is built from successive finite tests. No local orbit separation is used. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_simultaneous_bad_averages
    (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D))
    {k : ℕ} (T : Fin k → Y →L[𝕜] ShiftSpace D) {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 < ε) (hT : ∀ i, r < blockOperatorSeminorm D Y (T i))
    (B m : ℕ) (hk : k ≤ D.j (2*m+1)) :
    ∃ z : Fin k → C00 𝕜, ∃ y : Fin k → Y, ∃ φ : ShiftSpace D →L[𝕜] 𝕜,
      (∀ i, (y i : ShiftSpace D) = denseEmbedding D (z i)) ∧
      (∀ i, z i ∈ afterCutoff B) ∧ (∀ i, ‖y i‖ ≤ 4) ∧
      (∀ i (n : ℕ), 0 < n → (n : ℝ) ≤ Real.sqrt (D.j (2*m+1) : ℝ) →
        intervalNorm D n (z i) ≤ 8) ∧ ‖φ‖ ≤ 2 ∧
      ∀ i, r-ε ≤ RCLike.re (φ (T i (y i))) := by
  classical
  let N := D.j (2*m+1)
  have hN : 0 < N := D.j_positive _
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let η := ε / (((k : ℝ)+1)*N)
  have hη : 0 < η := div_pos hε (mul_pos (by positivity) hNr)
  obtain ⟨d⟩ := exists_norming_RIS_family D Y T hr hη hT T B N
  let u (i : Fin k) (n : Fin N) : Y := ⟨denseEmbedding D (d.vector i n),d.mem i n⟩
  let z (i : Fin k) := normalizedPairVector (d.vector i)
  let y (i : Fin k) : Y := normalizedPairSum (𝕜 := 𝕜) (u i)
  let φ := ∑ i, completedPairing D (averagedPairFunctional (d.functional i))
  have hval (i : Fin k) : (y i : ShiftSpace D) = denseEmbedding D (z i) :=
    normalizedPairSum_subspace_value D Y (u i) (d.vector i) (fun _ => rfl)
  have hgap : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ)) :=
    ⟨Real.log_le_self hNr.le,
      (show (N : ℝ) ≤ (N : ℝ)+1 by linarith).trans (Real.add_one_le_exp _)⟩
  refine ⟨z,y,φ,hval,?_,?_,?_,?_,?_⟩
  · intro i
    exact (afterCutoff B).smul_mem _ (Submodule.sum_mem _ (fun n _ => d.vector_after i n))
  · intro i
    rw [show ‖y i‖ = implicitNorm D (z i) from
      normalizedPairSum_subspace_norm D Y (u i) (d.vector i) (fun _ => rfl)]
    exact normalizedPairVector_norm_le_four (d.ris i) m hgap
  · intro i n hn hnN
    exact normalizedPairVector_intervalNorm_le_eight m (d.ris i) hn hnN
  · exact norm_sum_averagedPairing_le_two D hN hk d.functional
      d.successive d.successive_blocks d.dualUnit
  · intro i
    have hh := combined_average_re_lower_bound D hN d.functional (u i) (T i) i hη.le
      (fun n => (d.detected i n).le)
      (fun j s t hne => (d.cross j i s t hne i).le)
    have he : ((k : ℝ)+1)*N*η = ε := by
      dsimp only [η]
      field_simp
    simpa only [he] using hh

end ThesisCommon.GowersMaurey
