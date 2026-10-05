import Posets.CompactificationLiftMaps

noncomputable section
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Compression of operators to a complemented subspace, as a bounded linear map. -/
def cornerCompression (j : E →L[𝕜] F) (π : F →L[𝕜] E) :
    (F →L[𝕜] F) →L[𝕜] (E →L[𝕜] E) :=
  ((ContinuousLinearMap.compL 𝕜 E F E).flip j).comp
    (ContinuousLinearMap.compL 𝕜 F F E π)

@[simp] theorem cornerCompression_apply (j : E →L[𝕜] F) (π : F →L[𝕜] E)
    (T : F →L[𝕜] F) (x : E) : cornerCompression j π T x = π (T (j x)) := rfl

@[simp] theorem cornerCompression_section (j : E →L[𝕜] F) (π : F →L[𝕜] E)
    (hπj : π.comp j = ContinuousLinearMap.id 𝕜 E) (A : E →L[𝕜] E) :
    cornerCompression j π (cornerCompression π j A) = A := by
  have h (x : E) : π (j x) = x := DFunLike.congr_fun hπj x
  ext x
  simp [h]

/-- The scalar corner of a codimension-one splitting has finite rank. -/
theorem finiteDimensional_range_rankOne (ε : E →L[𝕜] 𝕜) (u : E) :
    FiniteDimensional 𝕜 (LinearMap.range (ε.smulRight u).toLinearMap) := by
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span 𝕜 {u})
  rintro _ ⟨x, rfl⟩
  exact Submodule.smul_mem _ (ε x) (Submodule.subset_span (by simp))

/-- Compression differs from preserving a product by a rank-one operator. -/
theorem cornerCompression_mul (j : E →L[𝕜] F) (π : F →L[𝕜] E)
    (ε : F →L[𝕜] 𝕜) (u : F) (hdecomp : ∀ f, j (π f) + ε f • u = f)
    (T S : F →L[𝕜] F) :
    cornerCompression j π (T * S) =
      cornerCompression j π T * cornerCompression j π S +
        (ε.comp (S.comp j)).smulRight (π (T u)) := by
  ext x
  change π (T (S (j x))) = π (T (j (π (S (j x))))) + ε (S (j x)) • π (T u)
  calc
    _ = π (T (j (π (S (j x))) + ε (S (j x)) • u)) :=
      congrArg (fun f => π (T f)) (hdecomp (S (j x))).symm
    _ = _ := by simp

variable {C : Type} [NormedRing C] [NormedAlgebra 𝕜 C]

/-- A homomorphism which kills finite-rank operators lifts across a split
one-dimensional extension, including preservation of its range and analytic properties. -/
theorem corner_homomorphism_lift (j : E →L[𝕜] F) (π : F →L[𝕜] E)
    (hπj : π.comp j = ContinuousLinearMap.id 𝕜 E)
    (ε : F →L[𝕜] 𝕜) (u : F) (hdecomp : ∀ f, j (π f) + ε f • u = f)
    (Ψ : (E →L[𝕜] E) →ₗ[𝕜] C) (hmul : IsMultiplicative 𝕜 Ψ)
    (hfin : ∀ T, FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap) → Ψ T = 0) :
    ∃ Φ : (F →L[𝕜] F) →ₗ[𝕜] C,
      IsMultiplicative 𝕜 Φ ∧ Set.range Φ = Set.range Ψ ∧
      (Continuous Φ ↔ Continuous Ψ) ∧ (IsCompactOperator Φ ↔ IsCompactOperator Ψ) ∧
      (Function.Surjective Ψ → Function.Surjective Φ) ∧ (¬ Continuous Ψ → ¬ Continuous Φ) := by
  let q := cornerCompression j π
  let s := cornerCompression π j
  let Φ := Ψ.comp q.toLinearMap
  have hs (A : E →L[𝕜] E) : Φ (s A) = Ψ A := by
    change Ψ (cornerCompression j π (cornerCompression π j A)) = Ψ A
    rw [cornerCompression_section j π hπj]
  have hcont : Continuous Φ ↔ Continuous Ψ := by
    constructor
    · intro h
      exact (show (fun A => Φ (s A)) = Ψ from funext hs) ▸ h.comp s.continuous
    · intro h
      exact h.comp q.continuous
  refine ⟨Φ, ?_, ?_, hcont, ?_, ?_, fun h hn => h (hcont.mp hn)⟩
  · intro T S
    change Ψ (cornerCompression j π (T * S)) = _
    rw [cornerCompression_mul j π ε u hdecomp, map_add,
      hfin _ (finiteDimensional_range_rankOne _ _), add_zero, hmul]
    rfl
  · apply Set.Subset.antisymm
    · rintro _ ⟨T, rfl⟩
      exact ⟨q T, rfl⟩
    · rintro _ ⟨A, rfl⟩
      exact ⟨s A, hs A⟩
  · constructor
    · intro h
      exact (show (fun A => Φ (s A)) = Ψ from funext hs) ▸ h.comp_clm s
    · intro h
      exact h.comp_clm q
  · intro h c
    obtain ⟨A, hA⟩ := h c
    exact ⟨s A, (hs A).trans hA⟩

end Posets
