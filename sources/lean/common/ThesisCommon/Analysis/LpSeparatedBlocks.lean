import ThesisCommon.Analysis.CoordinateMaskSubspaces

/-! Off-diagonal block vanishing and its all-vector consequence on actual
finite-exponent ℓp spaces. The final identity is proved using the genuine
finite-coordinate expansion, and is deliberately restricted to p < ∞.
-/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ ι X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A coordinate mask either preserves or kills an actual singleton vector. -/
theorem lpCoordinateProjection_single (A : Set Γ) (γ : Γ) (x : X) :
    lpCoordinateProjection (𝕜 := 𝕜) p A (lp.single p γ x) =
      if γ ∈ A then lp.single p γ x else 0 := by
  classical
  apply lp.ext
  funext δ
  by_cases hδγ : δ = γ
  · subst δ
    by_cases hγ : γ ∈ A <;> simp [lpCoordinateProjection_apply, hγ]
  · have hzero : (lp.single p γ x : lp (fun _ : Γ => X) p) δ = 0 :=
      lp.single_apply_ne (E := fun _ : Γ => X) p γ x hδγ
    by_cases hγ : γ ∈ A
    · rw [if_pos hγ, lpCoordinateProjection_apply, hzero]
      split_ifs <;> rfl
    · rw [if_neg hγ, lpCoordinateProjection_apply, hzero]
      split_ifs <;> rfl

/-- A singleton vector belongs to the supported subspace of any set
containing its coordinate. -/
theorem lp_single_mem_supported (A : Set Γ) {γ : Γ} (hγ : γ ∈ A) (x : X) :
    lp.single p γ x ∈ lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p A := by
  intro δ hδ
  apply lp.single_apply_ne
  intro heq
  subst δ
  exact hδ hγ

/-- Triangular block support rules out all interactions from earlier blocks
to later, disjoint blocks. -/
theorem lp_triangular_block_zero [LinearOrder ι]
    (P : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (B : ι → Set Γ) (hB : Pairwise (fun α β => Disjoint (B α) (B β)))
    (htri : ∀ α, ∀ x : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α),
      ∀ γ ∉ ⋃ β ≤ α, B β, P x γ = 0)
    {α β : ι} (hαβ : α < β) :
    ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
      (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext γ
  change lpCoordinateProjection p (B β) (P x) γ = 0
  by_cases hγ : γ ∈ B β
  · rw [lpCoordinateProjection_apply, if_pos hγ]
    apply htri α x γ
    intro hmem
    obtain ⟨δ, hδ⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨hδα, hγδ⟩ := Set.mem_iUnion.mp hδ
    exact Set.disjoint_left.mp (hB (ne_of_lt (lt_of_le_of_lt hδα hαβ))) hγδ hγ
  · simp only [lpCoordinateProjection_apply, if_neg hγ]

/-- Every vector supported on mutually noninteracting blocks has the
displayed diagonal identity. This asserts no invariance of their union. -/
theorem lp_block_diagonal_on_supported_union (hp : p ≠ ∞)
    (P : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (B : ι → Set Γ) (H : Set ι)
    (hdiag : ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
      ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
        (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL = 0)
    (z : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (⋃ α ∈ H, B α))
    {α : ι} (hα : α ∈ H) :
    lpCoordinateProjection (𝕜 := 𝕜) p (B α) (P z) =
      lpCoordinateProjection (𝕜 := 𝕜) p (B α)
        (P (lpCoordinateProjection (𝕜 := 𝕜) p (B α) z)) := by
  classical
  let R := lpCoordinateProjection (𝕜 := 𝕜) (X := X) p (B α)
  let L := R.comp P
  have hsingle (γ : Γ) : L (lp.single p γ (z.val γ)) =
      (L.comp R) (lp.single p γ (z.val γ)) := by
    by_cases hγα : γ ∈ B α
    · change L (lp.single p γ (z.val γ)) = L (R (lp.single p γ (z.val γ)))
      rw [show R (lp.single p γ (z.val γ)) = lp.single p γ (z.val γ) by
        exact (lpCoordinateProjection_single p (B α) γ (z.val γ)).trans (if_pos hγα)]
    · have hRzero : R (lp.single p γ (z.val γ)) = 0 := by
        exact (lpCoordinateProjection_single p (B α) γ (z.val γ)).trans (if_neg hγα)
      change L (lp.single p γ (z.val γ)) = L (R (lp.single p γ (z.val γ)))
      rw [hRzero, map_zero]
      by_cases hγH : γ ∈ ⋃ β ∈ H, B β
      · obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp hγH
        obtain ⟨hβH, hγβ⟩ := Set.mem_iUnion.mp hβ
        have hβα : β ≠ α := fun heq => hγα (heq ▸ hγβ)
        let x : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B β) :=
          ⟨lp.single p γ (z.val γ), lp_single_mem_supported p (B β) hγβ (z.val γ)⟩
        exact DFunLike.congr_fun (hdiag β hβH α hα hβα) x
      · simp only [z.property γ hγH, lp.single_zero, map_zero]
  have hleft := (L.continuous.tendsto z.val).comp (lp.hasSum_single hp z.val)
  have hright := ((L.comp R).continuous.tendsto z.val).comp (lp.hasSum_single hp z.val)
  change Tendsto (fun F : Finset Γ => L (∑ γ ∈ F, lp.single p γ (z.val γ)))
    atTop (𝓝 (L z.val)) at hleft
  have heq : (fun F : Finset Γ => L (∑ γ ∈ F, lp.single p γ (z.val γ))) =
      (fun F : Finset Γ => (L.comp R) (∑ γ ∈ F, lp.single p γ (z.val γ))) := by
    funext F
    simp only [map_sum, hsingle]
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end ThesisCommon
