import ThesisCommon.FixedPoint.kakutani
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! The compact-convex fixed-point step in Gowers--Maurey Lemma 9.
The parameter set and linear operator family are actual finite-dimensional
objects. Kakutani is proved in the imported, locally checked development. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 V X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

theorem compact_convex_operator_fixed_point
    (A : Set V) (hA : Convex ℝ A) (hcompact : IsCompact A) (hne : A.Nonempty)
    (L : V →L[ℝ] (X →L[𝕜] X)) (T : X →L[𝕜] X)
    (y : A → X) (hy : Continuous y) (r : ℝ)
    (hlocal : ∀ u : A, ∃ v ∈ A, ‖(T - L v) (y u)‖ ≤ r) :
    ∃ u : A, ‖(T - L u.val) (y u)‖ ≤ r := by
  let F : A → Set V := fun u => {v | v ∈ A ∧ ‖(T - L v) (y u)‖ ≤ r}
  have hcont : Continuous (fun z : A × V => (T - L z.2) (y z.1)) :=
    (continuous_const.sub (L.continuous.comp continuous_snd)).clm_apply
      (hy.comp continuous_fst)
  have hgraph : FixedPoint.closedGraph F := by
    change IsClosed {z : A × V | z.2 ∈ A ∧ ‖(T - L z.2) (y z.1)‖ ≤ r}
    exact (hcompact.isClosed.preimage continuous_snd).inter
      (isClosed_le hcont.norm continuous_const)
  have hf : ∀ u, F u ⊆ A ∧ Convex ℝ (F u) ∧ (F u).Nonempty := by
    intro u
    refine ⟨fun _ hv => hv.1, ?_, hlocal u⟩
    rintro v ⟨hv, hvbound⟩ w ⟨hw, hwbound⟩ a b ha hb hab
    refine ⟨hA hv hw ha hb hab, ?_⟩
    have he : (T - L (a • v + b • w)) (y u) =
        a • ((T - L v) (y u)) + b • ((T - L w) (y u)) := by
      simp only [map_add, map_smul, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      calc
        _ = (a+b) • (T (y u)) - (a • L v (y u) + b • L w (y u)) := by
          rw [hab, one_smul]
        _ = _ := by rw [add_smul, smul_sub, smul_sub]; abel
    rw [he]
    calc
      _ ≤ a * ‖(T - L v) (y u)‖ + b * ‖(T - L w) (y u)‖ := by
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
          using norm_add_le (a • ((T - L v) (y u))) (b • ((T - L w) (y u)))
      _ ≤ a*r + b*r := add_le_add
        (mul_le_mul_of_nonneg_left hvbound ha) (mul_le_mul_of_nonneg_left hwbound hb)
      _ = r := by rw [← add_mul, hab, one_mul]
  obtain ⟨u, hu⟩ := FixedPoint.kakutani_fixed_point A hA hcompact hne F hgraph hf
  exact ⟨u, hu.2⟩

end ThesisCommon
