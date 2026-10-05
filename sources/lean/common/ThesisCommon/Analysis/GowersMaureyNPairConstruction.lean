import ThesisCommon.Analysis.GowersMaureyNPairSizes
import ThesisCommon.Analysis.GowersMaureyRISSubsequence

/-! N-pairs genuinely selected from specified successive vectors and
specified successive dual-unit functionals. The odd construction size
is arbitrary; no already selected RIS or norm estimate is assumed. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_NPair_subsequence (D : ConstructionData 𝕜)
    (u a : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (ha : ∀ i j, i < j → Before (a i) (a j))
    (hu0 : ∀ i, u i ≠ 0)
    (hub : ∀ i, intervalNorm D (i+1) (u i) ≤ 1)
    (hau : ∀ i, DualUnit (implicitNorm D) (a i)) (m : ℕ) :
    ∃ b : Fin (D.j (2*m+1)) → ℕ, StrictMono b ∧
      IsRIS D 1 (fun i => u (b i)) ∧
      implicitNorm D (normalizedPairVector (fun i => u (b i))) ≤ 4 ∧
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.sqrt (D.j (2*m+1) : ℝ) →
        intervalNorm D n (normalizedPairVector (fun i => u (b i))) ≤ 8) ∧
      AveragedFunctional (implicitNorm D) (D.j (2*m+1))
        (averagedPairFunctional (fun i => a (b i))) ∧
      ‖completedPairing D (averagedPairFunctional (fun i => a (b i)))‖ ≤ 1 := by
  obtain ⟨b,hb,hRIS⟩ := exists_RIS_subsequence D u (fun i => i+1) hu hu0
    (fun i j hij => Nat.add_lt_add_right hij 1) hub (D.j (2*m+1))
    (ε := 1) (by norm_num) (le_refl 1)
  have hNp : (0 : ℝ) < D.j (2*m+1) := by exact_mod_cast D.j_positive _
  have hgap : (D.j (2*m+1) : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ)) :=
    ⟨Real.log_le_self hNp.le,
      (show (D.j (2*m+1) : ℝ) ≤ (D.j (2*m+1) : ℝ)+1 by linarith).trans (Real.add_one_le_exp _)⟩
  have havg := averagedPairFunctional_mem (D := D) (D.j_positive (2*m+1))
    (fun i j hij => ha _ _ (hb hij)) (fun i => hau (b i))
  exact ⟨b,hb,hRIS,normalizedPairVector_norm_le_four hRIS m hgap,
    fun n hn hnN => normalizedPairVector_intervalNorm_le_eight m hRIS hn hnN,
    havg,norm_completedPairing_le_one havg.dualUnit⟩

end ThesisCommon.GowersMaurey
