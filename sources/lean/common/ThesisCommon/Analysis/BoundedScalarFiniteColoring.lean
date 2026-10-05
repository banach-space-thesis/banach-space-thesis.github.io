import ThesisCommon.Analysis.FiniteDimensionalUnitBallNets

/-! A finite coloring of a bounded real/complex scalar disc by nearby actual
scalar representatives. The coloring is chosen before any matrix operator. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_bounded_scalar_coloring {K η : ℝ} (hK : 0 < K) (hη : 0 < η) :
    ∃ s : Finset 𝕜, s.Nonempty ∧ ∃ color : 𝕜 → s,
      ∀ z : 𝕜, ‖z‖ ≤ K → ‖z - (color z : 𝕜)‖ ≤ η := by
  classical
  obtain ⟨S, _, _, hcover⟩ := exists_unitBall_net_card_le 𝕜 𝕜 (div_pos hη hK)
  have hnormK : ‖(K : 𝕜)‖ = K := by rw [RCLike.norm_ofReal, abs_of_pos hK]
  have hK0 : (K : 𝕜) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hnormK]
    exact hK
  let s := S.image (fun w => (K : 𝕜) * w)
  have hrep (z : 𝕜) (hz : ‖z‖ ≤ K) : ∃ y ∈ s, ‖z - y‖ ≤ η := by
    let w := (K : 𝕜)⁻¹ * z
    have hw : ‖w‖ ≤ 1 := by
      dsimp [w]
      rw [norm_mul, norm_inv, hnormK, inv_mul_eq_div]
      exact (div_le_one hK).mpr hz
    obtain ⟨y, hy, hwy⟩ := hcover w hw
    refine ⟨(K : 𝕜) * y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    have heq : z - (K : 𝕜) * y = (K : 𝕜) * (w - y) := by
      dsimp [w]
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hK0, one_mul]
    rw [heq, norm_mul, hnormK]
    calc
      _ ≤ K * (η / K) := mul_le_mul_of_nonneg_left hwy hK.le
      _ = η := by field_simp
  obtain ⟨y₀, hy₀, _⟩ := hrep 0 (by simpa using hK.le)
  have chooseRep (z : 𝕜) : ∃ y : s, ‖z‖ ≤ K → ‖z - (y : 𝕜)‖ ≤ η := by
    by_cases hz : ‖z‖ ≤ K
    · obtain ⟨y, hy, hzy⟩ := hrep z hz
      exact ⟨⟨y, hy⟩, fun _ => hzy⟩
    · exact ⟨⟨y₀, hy₀⟩, fun h => (hz h).elim⟩
  choose color hcolor using chooseRep
  exact ⟨s, ⟨y₀, hy₀⟩, color, hcolor⟩

end ThesisCommon
