import ThesisCommon.Analysis.Primary
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! Quantitative factorisation calculus shared by both manuscripts.
The perturbation proof uses exactly the paper's Neumann-series correction.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem FactorsIdentityWith.mono {T : X →L[𝕜] Y} {C D : ℝ}
    (h : FactorsIdentityWith T Z C) (hCD : C ≤ D) : FactorsIdentityWith T Z D := by
  obtain ⟨U, V, heq, hn⟩ := h
  exact ⟨U, V, heq, hn.trans hCD⟩

theorem FactorsIdentityWith.forget_bound {T : X →L[𝕜] Y} {C : ℝ}
    (h : FactorsIdentityWith T Z C) : FactorsIdentity T Z := by
  obtain ⟨U, V, heq, _⟩ := h
  exact ⟨U, V, heq⟩

theorem factorsIdentity_iff_exists_bound (T : X →L[𝕜] Y) :
    FactorsIdentity T Z ↔ ∃ C : ℝ, 1 ≤ C ∧ FactorsIdentityWith T Z C := by
  constructor
  · rintro ⟨U, V, heq⟩
    exact ⟨max 1 (‖U‖ * ‖V‖), le_max_left _ _, U, V, heq, le_max_right _ _⟩
  · rintro ⟨_, _, h⟩
    exact h.forget_bound

theorem HasUPFP.hasPFP (h : HasUPFP 𝕜 X) : HasPFP 𝕜 X := by
  obtain ⟨C, _, hC⟩ := h
  intro T
  exact (hC T).imp FactorsIdentityWith.forget_bound FactorsIdentityWith.forget_bound

/-- Pull a factorisation through a compression A T B back to T. The factor
space may differ from the domain and codomain of T. -/
theorem FactorsIdentityWith.of_compression {T : X →L[𝕜] X}
    (A : X →L[𝕜] Y) (B : Y →L[𝕜] X) {C : ℝ}
    (h : FactorsIdentityWith ((A.comp T).comp B) Z C) :
    FactorsIdentityWith T Z (C * (‖A‖ * ‖B‖)) := by
  obtain ⟨U, V, heq, hn⟩ := h
  refine ⟨U.comp A, B.comp V, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using heq
  · calc
      ‖U.comp A‖ * ‖B.comp V‖ ≤ (‖U‖ * ‖A‖) * (‖B‖ * ‖V‖) :=
        mul_le_mul (U.opNorm_comp_le A) (B.opNorm_comp_le V)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖U‖ * ‖V‖) * (‖A‖ * ‖B‖) := by ring
      _ ≤ C * (‖A‖ * ‖B‖) :=
        mul_le_mul_of_nonneg_right hn (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- AB = I is exactly what makes the complementary branch transfer. -/
theorem compression_complement (T : X →L[𝕜] X)
    (A : X →L[𝕜] Y) (B : Y →L[𝕜] X)
    (hAB : A.comp B = ContinuousLinearMap.id 𝕜 Y) :
    (A.comp (ContinuousLinearMap.id 𝕜 X - T)).comp B =
      ContinuousLinearMap.id 𝕜 Y - (A.comp T).comp B := by
  ext y
  have hy := congrArg (fun f : Y →L[𝕜] Y => f y) hAB
  change A (B y - T (B y)) = y - A (T (B y))
  rw [map_sub]
  change A (B y) = y at hy
  rw [hy]

/-- UPFP 5.6 / LPCK 2.4. Generalized to factor an arbitrary Banach space Z
through maps X → Y. No nonzero-space or positive-C hypothesis is added.
The correction is the geometric inverse of I - (I - U S V). -/
theorem FactorsIdentityWith.perturb [CompleteSpace Z]
    {T S : X →L[𝕜] Y} {C : ℝ} (h : FactorsIdentityWith T Z C)
    (hsmall : C * ‖S - T‖ < 1 / 2) : FactorsIdentityWith S Z (2 * C) := by
  obtain ⟨U, V, heq, hnorm⟩ := h
  have hC : 0 ≤ C := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hnorm
  let F : Z →L[𝕜] Z := (U.comp S).comp V
  let E : Z →L[𝕜] Z := ContinuousLinearMap.id 𝕜 Z - F
  have hdiff : E = -((U.comp (S - T)).comp V) := by
    ext z
    have hz := congrArg (fun f : Z →L[𝕜] Z => f z) heq
    change z - U (S (V z)) = -U ((S - T) (V z))
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    change U (T (V z)) = z at hz
    rw [hz]
    abel
  have hE : ‖E‖ < 1 / 2 := by
    calc
      ‖E‖ = ‖(U.comp (S - T)).comp V‖ := by rw [hdiff, norm_neg]
      _ ≤ (‖U‖ * ‖S - T‖) * ‖V‖ :=
        ((U.comp (S - T)).opNorm_comp_le V).trans
          (mul_le_mul_of_nonneg_right (U.opNorm_comp_le _) (norm_nonneg _))
      _ = (‖U‖ * ‖V‖) * ‖S - T‖ := by ring
      _ ≤ C * ‖S - T‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ < 1 / 2 := hsmall
  have hE1 : ‖E‖ < 1 := by linarith
  let W : (Z →L[𝕜] Z)ˣ := Units.oneSub E hE1
  have hW : (W : Z →L[𝕜] Z) = F := by
    change ContinuousLinearMap.id 𝕜 Z - (ContinuousLinearMap.id 𝕜 Z - F) = F
    abel
  have hWnorm : ‖(↑W⁻¹ : Z →L[𝕜] Z)‖ ≤ 2 := by
    have hg := tsum_geometric_le_of_norm_lt_one E hE1
    have hid : ‖(1 : Z →L[𝕜] Z)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hpos : 0 < 1 - ‖E‖ := by linarith
    have hinv : (1 - ‖E‖)⁻¹ ≤ (2 : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      linarith
    change ‖∑' n : ℕ, E ^ n‖ ≤ 2
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
      _ ≤ (2 * ‖U‖) * ‖V‖ := by gcongr
      _ = 2 * (‖U‖ * ‖V‖) := by ring
      _ ≤ 2 * C := by gcongr

/-- Perturb either branch of a factorisation dichotomy. This is the common
argument in LPCK Corollary 2.5 and both preservation theorems. -/
theorem factorization_dichotomy_perturb [CompleteSpace X]
    {D S : X →L[𝕜] X} {C : ℝ}
    (h : FactorsIdentityWith D X C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - D) X C)
    (hsmall : C * ‖S - D‖ < 1 / 2) :
    FactorsIdentityWith S X (2 * C) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - S) X (2 * C) := by
  rcases h with h | h
  · exact Or.inl (h.perturb hsmall)
  · apply Or.inr
    apply h.perturb
    have heq : (ContinuousLinearMap.id 𝕜 X - S) -
        (ContinuousLinearMap.id 𝕜 X - D) = -(S - D) := by abel
    simpa only [heq, norm_neg] using hsmall

end ThesisCommon
