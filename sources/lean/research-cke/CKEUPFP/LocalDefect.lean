import CKEUPFP.OperatorFields

/-!
# Elementary properties of the local defect

These proofs certify that the real supremum in Definition 3.2 is over a
nonempty bounded set, and has precisely the order properties used in Section 3.
They do not assume that the supplied field is a representing-measure atom field.
-/

noncomputable section

universe u v w

namespace CKEUPFP

variable {𝕜 : Type u} [RCLike 𝕜]
variable {K : Type v} [TopologicalSpace K]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem vanishesOff_iff (O : Set K) (f : C(K, E)) :
    VanishesOff O f ↔ Set.EqOn f (fun _ => (0 : E)) Oᶜ := by
  rfl

theorem vanishesOff_zero (O : Set K) : VanishesOff O (0 : C(K, E)) := by
  intro s hs
  rfl

theorem vanishesOff_mono {O U : Set K} (hOU : O ⊆ U) {f : C(K, E)}
    (hf : VanishesOff O f) : VanishesOff U f := by
  intro s hs
  exact hf s (fun h => hs (hOU h))

theorem rowOperator_apply (T : C(K, E) →L[𝕜] C(K, E)) (t : K) (f : C(K, E)) :
    rowOperator T t f = T f t := rfl

variable [CompactSpace K]

theorem norm_rowOperator_le (T : C(K, E) →L[𝕜] C(K, E)) (t : K) :
    ‖rowOperator T t‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact ((T f).norm_coe_le_norm t).trans (T.le_opNorm f)

theorem defect_norm_le (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) (t : K) (f : C(K, E)) :
    ‖T f t - A t (f t)‖ ≤ (‖T‖ + ‖A t‖) * ‖f‖ := by
  calc
    ‖T f t - A t (f t)‖ ≤ ‖T f t‖ + ‖A t (f t)‖ := norm_sub_le _ _
    _ ≤ ‖T‖ * ‖f‖ + ‖A t‖ * ‖f‖ := add_le_add
      (((T f).norm_coe_le_norm t).trans (T.le_opNorm f))
      (((A t).le_opNorm (f t)).trans
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (norm_nonneg _)))
    _ = (‖T‖ + ‖A t‖) * ‖f‖ := (add_mul _ _ _).symm

theorem localDefect_set_nonempty (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) (O : Set K) (t : K) :
    ({r : ℝ | ∃ f : C(K, E), ‖f‖ ≤ 1 ∧ VanishesOff O f ∧
      r = ‖T f t - A t (f t)‖} : Set ℝ).Nonempty := by
  refine ⟨0, 0, ?_, vanishesOff_zero O, ?_⟩
  · simp
  · simp

theorem localDefect_set_bddAbove (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) (O : Set K) (t : K) :
    BddAbove {r : ℝ | ∃ f : C(K, E), ‖f‖ ≤ 1 ∧ VanishesOff O f ∧
      r = ‖T f t - A t (f t)‖} := by
  refine ⟨‖T‖ + ‖A t‖, ?_⟩
  rintro r ⟨f, hf, _, rfl⟩
  exact (defect_norm_le T A t f).trans
    ((mul_le_mul_of_nonneg_left hf (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
      (mul_one _))

theorem norm_sub_le_localDefect (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) (O : Set K) (t : K)
    (f : C(K, E)) (hf : ‖f‖ ≤ 1) (hO : VanishesOff O f) :
    ‖T f t - A t (f t)‖ ≤ localDefect T A O t := by
  exact le_csSup (localDefect_set_bddAbove T A O t) ⟨f, hf, hO, rfl⟩

theorem localDefect_nonneg (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) (O : Set K) (t : K) :
    0 ≤ localDefect T A O t := by
  have h := norm_sub_le_localDefect T A O t (0 : C(K, E))
    (by simp) (vanishesOff_zero O)
  simpa using h

theorem localDefect_le_norm_add (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) (O : Set K) (t : K) :
    localDefect T A O t ≤ ‖T‖ + ‖A t‖ := by
  apply csSup_le (localDefect_set_nonempty T A O t)
  rintro r ⟨f, hf, _, rfl⟩
  exact (defect_norm_le T A t f).trans
    ((mul_le_mul_of_nonneg_left hf (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
      (mul_one _))

theorem localDefect_mono (T : C(K, E) →L[𝕜] C(K, E))
    (A : K → E →L[𝕜] E) {O U : Set K} (hOU : O ⊆ U) (t : K) :
    localDefect T A O t ≤ localDefect T A U t := by
  apply csSup_le (localDefect_set_nonempty T A O t)
  rintro r ⟨f, hf, hO, rfl⟩
  exact norm_sub_le_localDefect T A U t f hf (vanishesOff_mono hOU hO)

end CKEUPFP
