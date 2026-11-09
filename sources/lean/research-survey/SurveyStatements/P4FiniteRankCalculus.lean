import SurveyStatements.P4Approximation

/-! Finite-rank calculus for maps between different normed spaces. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P4

universe u v w z
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type z} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem HasFiniteRank.comp_left {A : X →L[𝕜] Y} (hA : HasFiniteRank 𝕜 A)
    (S : Y →L[𝕜] Z) : HasFiniteRank 𝕜 (S.comp A) := by
  let F := LinearMap.range A.toLinearMap
  letI : FiniteDimensional 𝕜 F := hA
  let L : F →ₗ[𝕜] Z := S.toLinearMap.comp F.subtype
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L)
  rintro z ⟨x, rfl⟩
  exact ⟨⟨A x, ⟨x, rfl⟩⟩, rfl⟩

theorem HasFiniteRank.add_map {A B : X →L[𝕜] Y}
    (hA : HasFiniteRank 𝕜 A) (hB : HasFiniteRank 𝕜 B) : HasFiniteRank 𝕜 (A + B) := by
  letI : FiniteDimensional 𝕜 (LinearMap.range A.toLinearMap) := hA
  letI : FiniteDimensional 𝕜 (LinearMap.range B.toLinearMap) := hB
  apply Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap)
  rintro y ⟨x, rfl⟩
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

theorem HasFiniteRank.sub_map {A B : X →L[𝕜] Y}
    (hA : HasFiniteRank 𝕜 A) (hB : HasFiniteRank 𝕜 B) : HasFiniteRank 𝕜 (A - B) := by
  letI : FiniteDimensional 𝕜 (LinearMap.range A.toLinearMap) := hA
  letI : FiniteDimensional 𝕜 (LinearMap.range B.toLinearMap) := hB
  apply Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap)
  rintro y ⟨x, rfl⟩
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩)
    (Submodule.mem_sup_right ⟨x, rfl⟩)

theorem finiteRank_zero_map : HasFiniteRank 𝕜 (0 : X →L[𝕜] Y) := by
  unfold HasFiniteRank
  change FiniteDimensional 𝕜 (LinearMap.range (0 : X →ₗ[𝕜] Y))
  rw [LinearMap.range_zero]
  infer_instance

theorem HasFiniteRank.sum_map {ι : Type*} (F : Finset ι) (A : ι → X →L[𝕜] Y)
    (hA : ∀ n ∈ F, HasFiniteRank 𝕜 (A n)) : HasFiniteRank 𝕜 (∑ n ∈ F, A n) := by
  classical
  revert hA
  induction F using Finset.induction_on with
  | empty => intro hA; simpa using finiteRank_zero_map (𝕜 := 𝕜) (X := X) (Y := Y)
  | @insert n F hn ih =>
      intro hA
      rw [Finset.sum_insert hn]
      exact (hA n (Finset.mem_insert_self _ _)).add_map
        (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)))

end SurveyStatements.P4
