import ThesisCommon.Analysis.HajnalFreeSet
import ThesisCommon.Analysis.LpProjectionFactorSelection
import ThesisCommon.Analysis.EllOneColumnNorm

/-! Finite column interference gives a contractive compression close to a
diagonal operator on an arbitrary uncountable ell1 sum. -/
noncomputable section
open Set
open scoped ENNReal Cardinal
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def HasEllOneFiniteInterference : Prop :=
  ∀ (S : X →L[𝕜] EllOneSum Γ X) (ε : ℝ), 0 < ε →
    ∃ (F : Finset Γ) (J R : X →L[𝕜] X),
      ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧ R.comp J = ContinuousLinearMap.id 𝕜 X ∧
      ‖(lpCoordinateProjection (𝕜 := 𝕜) 1 (↑F : Set Γ)ᶜ).comp (S.comp J)‖ ≤ ε

theorem ellOne_diagonal_dichotomy_arbitrary
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ) {C : ℝ} (hC : 0 ≤ C)
    (hX : HasCPFP 𝕜 X C)
    (F : Γ → X →L[𝕜] X) (M : ℝ) (hM : 0 ≤ M) (hF : ∀ γ, ‖F γ‖ ≤ M) :
    FactorsIdentityWith (lpDiagonal 1 F M hM hF) (EllOneSum Γ X) C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - lpDiagonal 1 F M hM hF)
        (EllOneSum Γ X) C := by
  classical
  let D := lpDiagonal 1 F M hM hF
  apply lp_factor_dichotomy_of_selected_coordinates 1 (by simp) D univ ?_ hC
  · exact full_cardinal_factor_branch hΓ univ (by simp)
      (fun γ => lpCoordinateEntry 1 D γ γ) (fun γ _ => hX _)
  · intro α _ β _ hne
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext γ
    simp [D, lpCoordinateProjection_singleton, hne.symm]

set_option maxHeartbeats 800000 in
theorem ellOne_finite_interference_near_diagonal
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hcapture : HasEllOneFiniteInterference (𝕜 := 𝕜) (Γ := Γ) (X := X))
    (T : EllOneSum Γ X →L[𝕜] EllOneSum Γ X) (ε : ℝ) (hε : 0 < ε) :
    ∃ (U V : EllOneSum Γ X →L[𝕜] EllOneSum Γ X)
      (F : Γ → X →L[𝕜] X) (M : ℝ) (hM : 0 ≤ M) (hF : ∀ γ, ‖F γ‖ ≤ M),
      ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧ U.comp V = ContinuousLinearMap.id 𝕜 _ ∧
      ‖U.comp (T.comp V) - lpDiagonal 1 F M hM hF‖ ≤ ε := by
  classical
  let col (γ : Γ) := T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : Γ => X) 1 γ)
  choose F J R hJ hR hRJ htail using fun γ => hcapture (col γ) ε hε
  obtain ⟨H, hH, hfree⟩ := hajnal_free_set (fun γ => (↑(F γ) : Set Γ)) Cardinal.aleph0
    hΓ.le hΓ (fun γ => by simpa using Cardinal.nat_lt_aleph0 (F γ).card)
  obtain ⟨a⟩ := Cardinal.eq.mp hH.symm
  let e : Γ ↪ Γ := a.toEmbedding.trans (Function.Embedding.subtype H)
  have he (γ : Γ) : e γ ∈ H := (a γ).property
  let Jd := lpDiagonal 1 (fun γ => J (e γ)) 1 zero_le_one (fun γ => hJ (e γ))
  let Rd := lpDiagonal 1 (fun γ => R (e γ)) 1 zero_le_one (fun γ => hR (e γ))
  let V := (lpExtend (𝕜 := 𝕜) 1 e).comp Jd
  let U := Rd.comp (lpRestrict (𝕜 := 𝕜) 1 e)
  have hnV : ‖V‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul (norm_lpExtend_le e) (norm_lpDiagonal_le _ _ _ _)
        (norm_nonneg _) zero_le_one)
  have hnU : ‖U‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul (norm_lpDiagonal_le _ _ _ _) (norm_lpRestrict_le e)
        (norm_nonneg _) zero_le_one)
  have hUV : U.comp V = ContinuousLinearMap.id 𝕜 _ := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext γ
    change R (e γ) (lpExtend (𝕜 := 𝕜) 1 e (Jd x) (e γ)) = x γ
    rw [lpExtend_apply_image]
    exact DFunLike.congr_fun (hRJ (e γ)) (x γ)
  let S := U.comp (T.comp V)
  let G (γ : Γ) := lpCoordinateEntry 1 S γ γ
  have hG (γ : Γ) : ‖G γ‖ ≤ ‖S‖ := norm_lpCoordinateEntry_le 1 S γ γ
  let D := lpDiagonal 1 G ‖S‖ (norm_nonneg S) hG
  have hVsingle (γ : Γ) (x : X) : V (lp.single 1 γ x) = lp.single 1 (e γ) (J (e γ) x) := by
    apply lp.ext
    funext δ
    by_cases hδ : ∃ β, e β = δ
    · obtain ⟨β, rfl⟩ := hδ
      change lpExtend (𝕜 := 𝕜) 1 e (Jd (lp.single 1 γ x)) (e β) = _
      rw [lpExtend_apply_image]
      by_cases hβ : β = γ
      · subst β; simp [Jd]
      · simp [Jd, hβ, (fun h => hβ (e.injective h))]
    · change lpExtend (𝕜 := 𝕜) 1 e (Jd (lp.single 1 γ x)) δ = _
      rw [lpExtend_apply_of_not_mem_range 1 e _ hδ]
      exact (lp.single_apply_ne (E := fun _ : Γ => X) 1 (e γ) _
        (fun h => hδ ⟨γ, h.symm⟩)).symm
  have hn : ‖S - D‖ ≤ ε := by
    apply ellOne_opNorm_le_of_columns _ hε.le
    intro γ
    let B := lpCoordinateProjection (𝕜 := 𝕜) (X := X) 1 ({e γ} : Set Γ)ᶜ
    let Q := lpCoordinateProjection (𝕜 := 𝕜) (X := X) 1 (↑(F (e γ)) : Set Γ)ᶜ
    have heq : (S - D).comp (lp.singleContinuousLinearMap 𝕜 (fun _ : Γ => X) 1 γ) =
        U.comp (B.comp (Q.comp ((col (e γ)).comp (J (e γ))))) := by
      apply ContinuousLinearMap.ext
      intro x
      apply lp.ext
      funext β
      change S (lp.single 1 γ x) β - G β ((lp.single 1 γ x : EllOneSum Γ X) β) =
        R (e β) (B (Q (T (lp.single 1 (e γ) (J (e γ) x)))) (e β))
      by_cases hβ : β = γ
      · subst β
        simp [B, Q, G, lpCoordinateEntry_apply]
      · have hne : e β ≠ e γ := fun h => hβ (e.injective h)
        have hf : e β ∉ (↑(F (e γ)) : Set Γ) := (hfree (e β) (he β) (e γ) (he γ) hne).1
        simp only [lp.single_apply_ne (E := fun _ : Γ => X) 1 γ x hβ, map_zero, sub_zero]
        change R (e β) (T (V (lp.single 1 γ x)) (e β)) = _
        rw [hVsingle]
        simp [B, Q, hne, hf]
    rw [heq]
    have hb : ‖B‖ ≤ 1 := norm_lpCoordinateProjection_le 1 _
    have ht : ‖Q.comp ((col (e γ)).comp (J (e γ)))‖ ≤ ε := htail (e γ)
    calc
      _ ≤ ‖U‖ * ‖B.comp (Q.comp ((col (e γ)).comp (J (e γ))))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 * ε) := mul_le_mul hnU
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hb ht (norm_nonneg _) zero_le_one)) (norm_nonneg _) zero_le_one
      _ = ε := by ring
  exact ⟨U, V, G, ‖S‖, norm_nonneg S, hG, hnU, hnV, hUV, hn⟩

theorem ellOne_hasCPFP_of_finite_interference [CompleteSpace X]
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hcapture : HasEllOneFiniteInterference (𝕜 := 𝕜) (Γ := Γ) (X := X))
    {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 X C) :
    HasCPFP 𝕜 (EllOneSum Γ X) (2 * C) := by
  intro T
  have hc : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨U, V, F, M, hM, hF, hU, hV, hUV, hclose⟩ :=
    ellOne_finite_interference_near_diagonal hΓ hcapture T (1 / (4 * C)) (by positivity)
  have hd := ellOne_diagonal_dichotomy_arbitrary hΓ.le hc.le hX F M hM hF
  have hsmall : C * ‖U.comp (T.comp V) - lpDiagonal 1 F M hM hF‖ < 1 / 2 := by
    have hb := mul_le_mul_of_nonneg_left hclose hc.le
    have he : C * (1 / (4 * C)) = (1 / 4 : ℝ) := by field_simp
    rw [he] at hb
    linarith
  have hp := factorization_dichotomy_perturb hd hsmall
  have hnorm (S : EllOneSum Γ X →L[𝕜] EllOneSum Γ X)
      (hf : FactorsIdentityWith (U.comp (S.comp V)) (EllOneSum Γ X) (2 * C)) :
      FactorsIdentityWith S (EllOneSum Γ X) (2 * C) := by
    have hh : FactorsIdentityWith ((U.comp S).comp V) (EllOneSum Γ X) (2 * C) := by
      simpa only [ContinuousLinearMap.comp_assoc] using hf
    apply (hh.of_compression U V).mono
    have hu : ‖U‖ * ‖V‖ ≤ 1 := by
      simpa using mul_le_mul hU hV (norm_nonneg _) zero_le_one
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * C)
  rcases hp with hp | hp
  · exact Or.inl (hnorm T hp)
  · apply Or.inr
    apply hnorm (ContinuousLinearMap.id 𝕜 _ - T)
    have he : U.comp ((ContinuousLinearMap.id 𝕜 _ - T).comp V) =
        ContinuousLinearMap.id 𝕜 _ - U.comp (T.comp V) := by
      simpa only [ContinuousLinearMap.comp_assoc] using compression_complement T U V hUV
    rw [he]
    exact hp

end ThesisCommon
