import ThesisCommon.Analysis.QuantitativePrimary

/-! The Neumann correction with its sharp geometric bound, needed for C⁺-PFP
in Sections 3 and 6 of Primariness and the Primary Factorisation Property. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

/-- If C‖S-T‖ ≤ r < 1, correcting a factorisation of T costs at most 1/(1-r). -/
theorem FactorsIdentityWith.perturb_fraction {T S : X →L[𝕜] Y} {C r : ℝ}
    (h : FactorsIdentityWith T Z C) (hr : r < 1) (hsmall : C * ‖S - T‖ ≤ r) :
    FactorsIdentityWith S Z (C / (1 - r)) := by
  obtain ⟨U, V, heq, hnorm⟩ := h
  have hC : 0 ≤ C := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hnorm
  let F : Z →L[𝕜] Z := (U.comp S).comp V
  let E : Z →L[𝕜] Z := ContinuousLinearMap.id 𝕜 Z - F
  have hdiff : E = -((U.comp (S - T)).comp V) := by
    ext z
    have hz := DFunLike.congr_fun heq z
    change U (T (V z)) = z at hz
    change z - U (S (V z)) = -U ((S - T) (V z))
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    rw [hz]
    abel
  have hE : ‖E‖ ≤ r := by
    calc
      ‖E‖ = ‖(U.comp (S - T)).comp V‖ := by rw [hdiff, norm_neg]
      _ ≤ (‖U‖ * ‖S - T‖) * ‖V‖ :=
        ((U.comp (S - T)).opNorm_comp_le V).trans
          (mul_le_mul_of_nonneg_right (U.opNorm_comp_le _) (norm_nonneg _))
      _ = (‖U‖ * ‖V‖) * ‖S - T‖ := by ring
      _ ≤ C * ‖S - T‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ r := hsmall
  have hE1 : ‖E‖ < 1 := hE.trans_lt hr
  let W : (Z →L[𝕜] Z)ˣ := Units.oneSub E hE1
  have hW : (W : Z →L[𝕜] Z) = F := by
    change ContinuousLinearMap.id 𝕜 Z - (ContinuousLinearMap.id 𝕜 Z - F) = F
    abel
  have hWnorm : ‖(↑W⁻¹ : Z →L[𝕜] Z)‖ ≤ (1 - r)⁻¹ := by
    have hg := tsum_geometric_le_of_norm_lt_one E hE1
    have hid : ‖(1 : Z →L[𝕜] Z)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hinv : (1 - ‖E‖)⁻¹ ≤ (1 - r)⁻¹ :=
      inv_anti₀ (sub_pos.mpr hr) (sub_le_sub_left hE 1)
    change ‖∑' n : ℕ, E ^ n‖ ≤ (1 - r)⁻¹
    linarith
  refine ⟨(↑W⁻¹ : Z →L[𝕜] Z).comp U, V, ?_, ?_⟩
  · have hi : (↑W⁻¹ : Z →L[𝕜] Z).comp F = ContinuousLinearMap.id 𝕜 Z := by
      rw [← hW]
      exact W.inv_val
    simpa only [F, ContinuousLinearMap.comp_assoc] using hi
  · calc
      ‖(↑W⁻¹ : Z →L[𝕜] Z).comp U‖ * ‖V‖ ≤
          (‖(↑W⁻¹ : Z →L[𝕜] Z)‖ * ‖U‖) * ‖V‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ ((1 - r)⁻¹ * ‖U‖) * ‖V‖ := by gcongr
      _ = (‖U‖ * ‖V‖) * (1 - r)⁻¹ := by ring
      _ ≤ C * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right hnorm
        (inv_nonneg.mpr (sub_pos.mpr hr).le)
      _ = C / (1 - r) := (div_eq_mul_inv _ _).symm

/-- Exact limiting constant after arbitrarily accurate contractive compression.
This theorem is conditional on the reduction and model dichotomy, both of
which must be proved for the concrete space before claiming its C⁺-PFP. -/
theorem hasCPlusPFP_of_approximate_compressions [CompleteSpace X]
    {C : ℝ} (hC : 0 < C) (Model : (X →L[𝕜] X) → Prop)
    (hdichotomy : ∀ D, Model D → FactorsIdentityWith D X C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - D) X C)
    (hreduction : ∀ (T : X →L[𝕜] X) (η : ℝ), 0 < η →
      ∃ A B D : X →L[𝕜] X,
        A.comp B = ContinuousLinearMap.id 𝕜 X ∧
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ Model D ∧ ‖(A.comp T).comp B - D‖ < η) :
    HasCPlusPFP 𝕜 X C := by
  intro ε hε T
  let r := ε / (C + ε)
  have hden : 0 < C + ε := add_pos hC hε
  have hrpos : 0 < r := div_pos hε hden
  have hr : r < 1 := (div_lt_one hden).mpr (by linarith)
  have hconst : C / (1 - r) = C + ε := by
    apply (div_eq_iff (sub_pos.mpr hr).ne').mpr
    dsimp [r]
    field_simp [hden.ne']
    ring
  obtain ⟨A, B, D, hAB, hnA, hnB, hD, he⟩ := hreduction T (r / C) (div_pos hrpos hC)
  have hsmall : C * ‖(A.comp T).comp B - D‖ ≤ r := by
    have hmul := mul_lt_mul_of_pos_left he hC
    have heq : C * (r / C) = r := by field_simp
    rw [heq] at hmul
    exact hmul.le
  have transfer (S : X →L[𝕜] X) (h : FactorsIdentityWith ((A.comp S).comp B) X (C + ε)) :
      FactorsIdentityWith S X (C + ε) := by
    apply (h.of_compression A B).mono
    have hn : ‖A‖ * ‖B‖ ≤ 1 := by
      simpa using mul_le_mul hnA hnB (norm_nonneg _) zero_le_one
    simpa using mul_le_mul_of_nonneg_left hn hden.le
  rcases hdichotomy D hD with h | h
  · left
    apply transfer T
    simpa only [hconst] using h.perturb_fraction hr hsmall
  · right
    apply transfer (ContinuousLinearMap.id 𝕜 X - T)
    rw [compression_complement T A B hAB]
    have hsmall' : C * ‖(ContinuousLinearMap.id 𝕜 X - (A.comp T).comp B) -
        (ContinuousLinearMap.id 𝕜 X - D)‖ ≤ r := by
      simpa only [sub_sub_sub_cancel_left, norm_sub_rev] using hsmall
    simpa only [hconst] using h.perturb_fraction hr hsmall'

end ThesisCommon
