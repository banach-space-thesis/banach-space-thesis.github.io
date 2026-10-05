import ThesisCommon.Analysis.OperatorAlgebraLpSelfCopies

/-! Fubini reordering for actual heterogeneous ell-one sums. In particular,
countable isometric self-similarity of every fibre gives exact self-copies
of the entire arbitrary-index sum. No classification of the fibres is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 ι κ : Type*} [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

theorem ellOneFamily_pair_summable (x : lp (fun i => lp (fun _ : κ => E i) 1) 1) :
    Summable (fun ij : ι × κ => ‖x ij.1 ij.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro i
    simpa using (lp.memℓp (x i)).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  · have hs : Summable (fun i => ‖x i‖) := by
      simpa using (lp.memℓp x).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
    apply hs.congr
    intro i
    simpa using lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) (x i)

def ellOneFamilyTransposeValue (x : lp (fun i => lp (fun _ : κ => E i) 1) 1) :
    lp (fun _ : κ => lp E 1) 1 := by
  have hpair : Summable (fun ji : κ × ι => ‖x ji.2 ji.1‖) :=
    (Equiv.prodComm κ ι).summable_iff.mpr (ellOneFamily_pair_summable x)
  have hs := (summable_prod_of_nonneg (fun _ : κ × ι => norm_nonneg _)).mp hpair
  let y : κ → lp E 1 := fun j => ⟨fun i => x i j, memℓp_gen (by simpa using hs.1 j)⟩
  refine ⟨y, memℓp_gen ?_⟩
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply hs.2.congr
  intro j
  simpa using (lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) (y j)).symm

@[simp] theorem ellOneFamilyTransposeValue_apply
    (x : lp (fun i => lp (fun _ : κ => E i) 1) 1) (j : κ) (i : ι) :
    ellOneFamilyTransposeValue x j i = x i j := rfl

theorem ellOneFamilyTransposeValue_norm
    (x : lp (fun i => lp (fun _ : κ => E i) 1) 1) :
    ‖ellOneFamilyTransposeValue x‖ = ‖x‖ := by
  have hpair := ellOneFamily_pair_summable x
  have hpair' : Summable (fun ji : κ × ι => ‖x ji.2 ji.1‖) :=
    (Equiv.prodComm κ ι).summable_iff.mpr hpair
  simp only [lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal),
    ENNReal.toReal_one, div_one, Real.rpow_one, ellOneFamilyTransposeValue_apply]
  exact hpair'.tsum_prod.symm.trans ((Equiv.prodComm κ ι).tsum_eq _ |>.trans hpair.tsum_prod)

def ellOneFamilyTranspose :
    lp (fun i => lp (fun _ : κ => E i) 1) 1 ≃ₗᵢ[𝕜] lp (fun _ : κ => lp E 1) 1 where
  toFun := ellOneFamilyTransposeValue
  invFun x := by
    have hpair : Summable (fun ji : κ × ι => ‖x ji.1 ji.2‖) := by
      apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      constructor
      · intro j
        simpa using (lp.memℓp (x j)).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
      · have hs : Summable (fun j => ‖x j‖) := by
          simpa using (lp.memℓp x).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
        apply hs.congr
        intro j
        simpa using lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) (x j)
    have hpair' : Summable (fun ij : ι × κ => ‖x ij.2 ij.1‖) :=
      (Equiv.prodComm ι κ).summable_iff.mpr hpair
    have hs := (summable_prod_of_nonneg (fun _ : ι × κ => norm_nonneg _)).mp hpair'
    let y : ∀ i, lp (fun _ : κ => E i) 1 := fun i =>
      ⟨fun j => x j i, memℓp_gen (by simpa using hs.1 i)⟩
    refine ⟨y, memℓp_gen ?_⟩
    simp only [ENNReal.toReal_one, Real.rpow_one]
    apply hs.2.congr
    intro i
    simpa using (lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) (y i)).symm
  left_inv x := by apply lp.ext; funext i; apply lp.ext; funext j; rfl
  right_inv x := by apply lp.ext; funext j; apply lp.ext; funext i; rfl
  map_add' x y := by apply lp.ext; funext j; apply lp.ext; funext i; rfl
  map_smul' a x := by apply lp.ext; funext j; apply lp.ext; funext i; rfl
  norm_map' := ellOneFamilyTransposeValue_norm

theorem exists_orthogonal_selfCopies_ellOne_family
    (e : ∀ i, E i ≃ₗᵢ[𝕜] lp (fun _ : ℕ => E i) 1) :
    ∃ J P : ℕ → lp E 1 →L[𝕜] lp E 1,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  let d := (lebesgueLpCoordinateEquiv (by simp : 0 < (1 : ℝ≥0∞).toReal) e).trans
    (ellOneFamilyTranspose (𝕜 := 𝕜))
  exact exists_orthogonal_selfCopies_of_sequence_equiv d.toContinuousLinearEquiv

end ThesisCommon
