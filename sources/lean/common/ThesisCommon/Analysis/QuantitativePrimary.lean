import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Exact quantitative definitions and isomorphism transport for
Acuaviva--Kania, Primariness and the Primary Factorisation Property, §2. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The C⁺-PFP means every strictly larger constant works. It does not assert
that the endpoint C itself is attained. The paper uses C ≥ 1. -/
def HasCPlusPFP (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasCPFP 𝕜 X (C + ε)

theorem HasCPlusPFP.hasUPFP {C : ℝ} (hC : 1 ≤ C)
    (h : HasCPlusPFP 𝕜 X C) : HasUPFP 𝕜 X :=
  ⟨C + 1, by linarith, h 1 zero_lt_one⟩

/-- Proposition 2.5, with the exact printed constant and conjugated witnesses.
No completeness or nontriviality assumption is needed for this algebraic step. -/
theorem HasCPFP.of_equiv_exact {C : ℝ} (h : HasCPFP 𝕜 Y C) (e : X ≃L[𝕜] Y) :
    HasCPFP 𝕜 X (C * ‖e.toContinuousLinearMap‖ ^ 2 *
      ‖e.symm.toContinuousLinearMap‖ ^ 2) := by
  let A := e.toContinuousLinearMap
  let B := e.symm.toContinuousLinearMap
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 Y := by
    ext y
    exact e.apply_symm_apply y
  have liftFactor (T : X →L[𝕜] X)
      (hT : FactorsIdentityWith ((A.comp T).comp B) Y C) :
      FactorsIdentityWith T X (C * ‖e.toContinuousLinearMap‖ ^ 2 *
        ‖e.symm.toContinuousLinearMap‖ ^ 2) := by
    have h' := (hT.of_compression A B).target_equiv e.symm
    convert h' using 1
    dsimp [A, B]
    ring
  intro T
  rcases h ((A.comp T).comp B) with hT | hT
  · exact Or.inl (liftFactor T hT)
  · apply Or.inr
    apply liftFactor (ContinuousLinearMap.id 𝕜 X - T)
    rwa [compression_complement T A B hAB]

/-- Lemma 5.3: a boundedly invertible restriction onto a complemented range
supplies the actual factors. Complementability of Y is not used in the proof. -/
theorem factorsIdentity_of_complemented_restriction
    (S : X →L[𝕜] X) (Y Z : Submodule 𝕜 X)
    (V : X ≃L[𝕜] Y) (W : Y ≃L[𝕜] Z)
    (hW : ∀ y : Y, (W y : X) = S y)
    (P : X →L[𝕜] Z) (hP : ∀ z : Z, P z = z) : FactorsIdentity S X := by
  refine ⟨(V.symm.toContinuousLinearMap.comp W.symm.toContinuousLinearMap).comp P,
    Y.subtypeL.comp V.toContinuousLinearMap, ?_⟩
  ext x
  change V.symm (W.symm (P (S (V x)))) = x
  rw [← hW (V x), hP, W.symm_apply_apply, V.symm_apply_apply]

end ThesisCommon
