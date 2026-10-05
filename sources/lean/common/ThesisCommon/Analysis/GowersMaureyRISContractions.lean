import ThesisCommon.Analysis.GowersMaureyCodedPairOuterRIS

/-! Positive scalar contractions preserve genuine RIS data, including the
support spacing clauses. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def RISData.real_smul {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    RISData D ε (fun i => r • x i) where
  epsilon_pos := h.epsilon_pos
  epsilon_le_one := h.epsilon_le_one
  successive := successive_real_smul h.successive r
  size := h.size
  size_strict := h.size_strict
  size_pos := h.size_pos
  first_large := h.first_large
  norm_bound i := by
    rw [seminorm_real_smul, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (h.norm_bound i) hr.le).trans (by simpa using hr1)
  spacing i hi := by
    rw [prefixSum_real_smul, supportInterval_real_smul hr.ne']
    exact h.spacing i hi

theorem IsRIS.real_smul {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : IsRIS D ε x) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    IsRIS D ε (fun i => r • x i) := by
  obtain ⟨h⟩ := h
  exact ⟨h.real_smul hr hr1⟩

end ThesisCommon.GowersMaurey
