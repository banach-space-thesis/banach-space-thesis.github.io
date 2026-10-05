import Posets.MrowkaContinuity

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology ThesisCommon
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 ℬ : Set (Set ℕ)}

/-- Extension by zero at newly adjoined family points; natural points are retained. -/
def extensionValue (f : Space 𝕜 𝒜) : Mrowka ℬ → 𝕜
  | .inl n => f (Sum.inl n)
  | .inr B => if hB : B.val ∈ 𝒜 then f (Sum.inr ⟨B.val, hB⟩) else 0

theorem extensionValue_inclusion (h : 𝒜 ⊆ ℬ) (f : Space 𝕜 𝒜) (p : Mrowka 𝒜) :
    extensionValue f (pointInclusion h p) = f p := by
  cases p with
  | inl n => rfl
  | inr A => simp [extensionValue, pointInclusion, A.property]

theorem extensionValue_continuous (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ)
    (f : Space 𝕜 𝒜) : Continuous (extensionValue (ℬ := ℬ) f) := by
  apply (mrowka_continuous_iff _).mpr
  intro B
  by_cases hB : B.val ∈ 𝒜
  · simpa only [extensionValue, dif_pos hB] using
      f.continuous.continuousAt.tendsto.comp (family_tendsto_along 𝒜 ⟨B.val, hB⟩)
  · have hbig : IsAlmostDisjoint (insert B.val 𝒜) := by
      have hsub : insert B.val 𝒜 ⊆ ℬ := Set.insert_subset B.property h
      exact ⟨fun A hA => hℬ.1 A (hsub hA),
        fun A hA C hC hAC => hℬ.2 A (hsub hA) C (hsub hC) hAC⟩
    simpa only [extensionValue, dif_neg hB] using
      (zero_at_infty f).comp (natural_tendsto_cocompact hB hbig)

theorem extensionValue_zeroAtInfty (h : 𝒜 ⊆ ℬ) (f : Space 𝕜 𝒜) :
    Tendsto (extensionValue (ℬ := ℬ) f) (cocompact (Mrowka ℬ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK, hsmall⟩ := hasBasis_cocompact.mem_iff.mp
    ((Metric.tendsto_nhds.mp (zero_at_infty f)) ε hε)
  filter_upwards [(hK.image (pointInclusion_continuous h)).compl_mem_cocompact] with p hp
  cases p with
  | inl n =>
    apply hsmall
    intro hn
    exact hp ⟨Sum.inl n, hn, rfl⟩
  | inr B =>
    by_cases hB : B.val ∈ 𝒜
    · change dist (if _ : B.val ∈ 𝒜 then f (Sum.inr ⟨B.val, hB⟩) else 0) 0 < ε
      rw [dif_pos hB]
      apply hsmall
      intro hBK
      exact hp ⟨Sum.inr ⟨B.val, hB⟩, hBK, rfl⟩
    · simpa [extensionValue, hB] using hε

def canonicalExtension (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ) (f : Space 𝕜 𝒜) : Space 𝕜 ℬ where
  toFun := extensionValue f
  continuous_toFun := extensionValue_continuous h hℬ f
  zero_at_infty' := extensionValue_zeroAtInfty h f

theorem norm_canonicalExtension_le (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ)
    (f : Space 𝕜 𝒜) : ‖canonicalExtension h hℬ f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro p
  cases p with
  | inl n => exact f.toBCF.norm_coe_le_norm (Sum.inl n)
  | inr B =>
    change ‖extensionValue f (Sum.inr B)‖ ≤ ‖f‖
    by_cases hB : B.val ∈ 𝒜
    · simpa only [extensionValue, dif_pos hB] using f.toBCF.norm_coe_le_norm (Sum.inr ⟨B.val, hB⟩)
    · simp [extensionValue, hB]

/-- The concrete bounded algebra homomorphism of Remark 4.9. -/
def canonicalEmbedding (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ) : BoundedHom 𝕜 (Space 𝕜 𝒜) (Space 𝕜 ℬ) where
  toContinuousLinearMap :=
    ({toFun := canonicalExtension h hℬ
      map_add' := by
        intro f g
        ext p
        cases p with
        | inl n => rfl
        | inr B => by_cases hB : B.val ∈ 𝒜 <;>
            simp [canonicalExtension, extensionValue, hB]
      map_smul' := by
        intro a f
        ext p
        cases p with
        | inl n => rfl
        | inr B => by_cases hB : B.val ∈ 𝒜 <;>
            simp [canonicalExtension, extensionValue, hB]} : Space 𝕜 𝒜 →ₗ[𝕜] Space 𝕜 ℬ).mkContinuous
        1 (fun f => by simpa using norm_canonicalExtension_le h hℬ f)
  map_mul' := by
    intro f g
    ext p
    cases p with
    | inl n => rfl
    | inr B => by_cases hB : B.val ∈ 𝒜 <;>
        simp [canonicalExtension, extensionValue, hB]

theorem canonicalEmbedding_isometry (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ) :
    Isometry (canonicalEmbedding (𝕜 := 𝕜) h hℬ) := by
  apply AddMonoidHomClass.isometry_of_norm (canonicalEmbedding h hℬ).toContinuousLinearMap
  intro f
  apply le_antisymm (norm_canonicalExtension_le h hℬ f)
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (canonicalExtension h hℬ f))).mpr
  intro p
  have hp := (canonicalExtension h hℬ f).toBCF.norm_coe_le_norm (pointInclusion h p)
  change ‖extensionValue f (pointInclusion h p)‖ ≤ _ at hp
  rwa [extensionValue_inclusion] at hp

theorem canonicalEmbeddingExists_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 ℬ : Set (Set ℕ)) :
    CanonicalEmbeddingExists 𝕜 𝒜 ℬ := by
  intro _ hℬ h
  refine ⟨canonicalEmbedding h hℬ, canonicalEmbedding_isometry h hℬ, ?_, ?_⟩
  · intros; rfl
  · intros; rfl

@[simp] theorem canonicalEmbedding_natural (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ)
    (f : Space 𝕜 𝒜) (n : ℕ) : canonicalEmbedding h hℬ f (Sum.inl n) = f (Sum.inl n) := rfl

@[simp] theorem canonicalEmbedding_family (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ)
    (f : Space 𝕜 𝒜) (B : ℬ) :
    canonicalEmbedding h hℬ f (Sum.inr B) =
      if hB : B.val ∈ 𝒜 then f (Sum.inr ⟨B.val, hB⟩) else 0 := rfl

theorem canonicalEmbedding_self (h𝒜 : IsAlmostDisjoint 𝒜) :
    (canonicalEmbedding (𝕜 := 𝕜) (Set.Subset.refl 𝒜) h𝒜).toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 (Space 𝕜 𝒜) := by
  ext f p
  cases p with
  | inl n => rfl
  | inr A => simp [canonicalEmbedding, canonicalExtension, extensionValue, A.property]

/-- The coherence law required in Theorem 1.1 holds for the actual operators. -/
theorem canonicalEmbedding_comp {𝒞 : Set (Set ℕ)} (hAB : 𝒜 ⊆ ℬ) (hBC : ℬ ⊆ 𝒞)
    (hℬ : IsAlmostDisjoint ℬ) (h𝒞 : IsAlmostDisjoint 𝒞) :
    (canonicalEmbedding (𝕜 := 𝕜) hBC h𝒞).toContinuousLinearMap.comp
      (canonicalEmbedding hAB hℬ).toContinuousLinearMap =
      (canonicalEmbedding (hAB.trans hBC) h𝒞).toContinuousLinearMap := by
  ext f p
  cases p with
  | inl n => rfl
  | inr C =>
    by_cases hCA : C.val ∈ 𝒜
    · have hCB := hAB hCA
      simp [canonicalEmbedding, canonicalExtension, extensionValue, hCA, hCB]
    · by_cases hCB : C.val ∈ ℬ <;>
        simp [canonicalEmbedding, canonicalExtension, extensionValue, hCA, hCB]

theorem reducedMatrix_canonicalEmbedding (h : 𝒜 ⊆ ℬ) (hℬ : IsAlmostDisjoint ℬ) :
    reducedMatrix 𝕜 (canonicalEmbedding h hℬ).toContinuousLinearMap = identityMatrix 𝕜 := by
  funext k n
  exact isolatedVector_natural 𝕜 𝒜 n k

end Posets
