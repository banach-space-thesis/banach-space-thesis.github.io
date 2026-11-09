import UPFP.PrintedL1

/-! UPFP Lemma 6.5 with actual measurable sets and varying L₁ fibers. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Cardinal
namespace UPFP.Printed
open ThesisCommon
set_option maxHeartbeats 2400000
variable {𝕜 Λ : Type*} [RCLike 𝕜]

private theorem family_column_norm_le {ι Y : Type*} {X : ι → Type*}
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [DecidableEq ι]
    (T : lp X 1 →L[𝕜] Y) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ i x, ‖T (lp.single 1 i x)‖ ≤ ε * ‖x‖) : ‖T‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  have hs := (lp.hasSum_single (p := 1) (by simp) x).map T.toAddMonoidHom T.continuous
  have hn : HasSum (fun i => ‖x i‖) ‖x‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using lp.hasSum_norm (p := 1) (by simp) x
  exact hs.norm_le_of_bounded (hn.mul_left ε) (fun i => hT i (x i))

/-- The conclusion of the printed Lemma 6.5, with the genuine varying
fibres, cardinal equality, canonical restriction and zero extension. -/
def DiagonalReductionConclusion
    (T : EllOneSum Λ (IntervalL1 𝕜) →L[𝕜] EllOneSum Λ (IntervalL1 𝕜)) (ε : ℝ) : Prop :=
  ∃ (H : Set Λ) (B : H → Set UnitInterval),
    Cardinal.mk H = Cardinal.mk Λ ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < volume (B i)) ∧
    ∃ (V : lp (fun i => IntervalL1Part 𝕜 (B i)) 1 →L[𝕜] EllOneSum H (IntervalL1 𝕜))
      (U : EllOneSum H (IntervalL1 𝕜) →L[𝕜] lp (fun i => IntervalL1Part 𝕜 (B i)) 1)
      (D : lp (fun i => IntervalL1Part 𝕜 (B i)) 1 →L[𝕜]
        lp (fun i => IntervalL1Part 𝕜 (B i)) 1),
      ‖V‖ ≤ 1 ∧ ‖U‖ ≤ 1 ∧ U.comp V = ContinuousLinearMap.id 𝕜 _ ∧
      (∃ G : ∀ i, IntervalL1Part 𝕜 (B i) →L[𝕜] IntervalL1Part 𝕜 (B i),
        ∀ x i, D x i = G i (x i)) ∧
      ‖(U.comp (((lpRestrict 1 (Function.Embedding.subtype H)).comp T).comp
        (lpExtend 1 (Function.Embedding.subtype H)))).comp V - D‖ ≤ ε

private theorem extend_single {ι κ Y : Type*} [DecidableEq ι] [DecidableEq κ]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (e : ι ↪ κ) (i : ι) (x : Y) :
    lpExtend (𝕜 := 𝕜) 1 e (lp.single 1 i x) = lp.single 1 (e i) x := by
  apply lp.ext
  funext k
  by_cases hk : ∃ j, e j = k
  · obtain ⟨j, rfl⟩ := hk
    rw [lpExtend_apply_image]
    by_cases h : j = i
    · subst j; simp
    · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ (fun he => h (e.injective he))]
  · change Function.extend e (lp.single (E := fun _ : ι => Y) 1 i x)
        (fun _ => 0) k = lp.single (E := fun _ : κ => Y) 1 (e i) x k
    rw [Function.extend_apply' _ _ _ hk, lp.single_apply_ne _ _ _ (fun he => hk ⟨i, he.symm⟩)]

private theorem localized_diagonal (hΛ : Cardinal.aleph0 < Cardinal.mk Λ)
    (T : EllOneSum Λ (IntervalL1 𝕜) →L[𝕜] EllOneSum Λ (IntervalL1 𝕜)) {ε : ℝ}
    (hε : 0 < ε)
    (capture : ∀ S : IntervalL1 𝕜 →L[𝕜] EllOneSum Λ (IntervalL1 𝕜),
      ∃ (F : Finset Λ) (B : Set UnitInterval) (hB : MeasurableSet B),
        0 < volume B ∧ ‖(lpCoordinateProjection 1 (↑F : Set Λ)ᶜ).comp
          (S.comp (intervalPartExtend (𝕜 := 𝕜) B hB))‖ < ε) :
    DiagonalReductionConclusion T ε := by
  classical
  let col (i : Λ) := T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : Λ => IntervalL1 𝕜) 1 i)
  choose F B hB hp hc using fun i => capture (col i)
  obtain ⟨H, hH, hfree⟩ := hajnal_free_set (fun i => (↑(F i) : Set Λ)) Cardinal.aleph0
    hΛ.le hΛ (fun i => by simpa using Cardinal.nat_lt_aleph0 (F i).card)
  let E (i : H) : Type _ := IntervalL1Part 𝕜 (B i.val)
  let J (i : H) : E i →L[𝕜] IntervalL1 𝕜 :=
    intervalPartExtend (B i.val) (hB i.val)
  let R (i : H) : IntervalL1 𝕜 →L[𝕜] E i := lebesgueLpRestrict (𝕜 := 𝕜) (B i.val)
  have hj (i : H) : ‖J i‖ ≤ 1 :=
    norm_intervalPartExtend_le _ _
  have hr (i : H) : ‖R i‖ ≤ 1 := norm_lebesgueLpRestrict_le _
  let V : lp E 1 →L[𝕜] EllOneSum H (IntervalL1 𝕜) :=
    lpFamilyDiagonal (𝕜 := 𝕜) (E := E) (F := fun _ : H => IntervalL1 𝕜) (p := 1)
      J 1 zero_le_one hj
  let U : EllOneSum H (IntervalL1 𝕜) →L[𝕜] lp E 1 :=
    lpFamilyDiagonal (𝕜 := 𝕜) (E := fun _ : H => IntervalL1 𝕜) (F := E) (p := 1)
      R 1 zero_le_one hr
  let keep : EllOneSum Λ (IntervalL1 𝕜) →L[𝕜] EllOneSum H (IntervalL1 𝕜) :=
    lpRestrict 1 (Function.Embedding.subtype H)
  let insertH : EllOneSum H (IntervalL1 𝕜) →L[𝕜] EllOneSum Λ (IntervalL1 𝕜) :=
    lpExtend 1 (Function.Embedding.subtype H)
  let S : lp E 1 →L[𝕜] lp E 1 := (U.comp ((keep.comp T).comp insertH)).comp V
  have hpoint (i : H) : ∀ x : E i, ‖S (lp.single 1 i x) i‖ ≤ ‖S‖ * ‖x‖ := by
    intro x
    let y : lp E 1 := lp.single (E := E) 1 i x
    have hy : ‖y‖ = ‖x‖ := lp.norm_single (by simp : (0 : ℝ≥0∞) < 1) i x
    have h₁ : ‖S y i‖ ≤ ‖S y‖ :=
      lp.norm_apply_le_norm (E := E) (p := 1) (by simp) (S y) i
    exact h₁.trans ((S.le_opNorm y).trans_eq (congrArg (‖S‖ * ·) hy))
  let G (i : H) : E i →L[𝕜] E i := LinearMap.mkContinuous
    { toFun := fun x => S (lp.singleContinuousLinearMap 𝕜 E 1 i x) i
      map_add' := fun x y => by simp only [map_add, lp.coeFn_add, Pi.add_apply]
      map_smul' := fun c x => by simp only [map_smul, lp.coeFn_smul, Pi.smul_apply,
        RingHom.id_apply] } ‖S‖ (hpoint i)
  have hG (i : H) : ‖G i‖ ≤ ‖S‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  let D : lp E 1 →L[𝕜] lp E 1 :=
    lpFamilyDiagonal (𝕜 := 𝕜) (E := E) (F := E) (p := 1) G ‖S‖ (norm_nonneg S) hG
  have hUV : U.comp V = ContinuousLinearMap.id 𝕜 _ := by
    ext x : 1
    apply lp.ext
    funext i
    exact lebesgueLpRestrict_extend (B i.val) (hB i.val) (x i)
  have hV : ‖V‖ ≤ 1 := lpFamilyDiagonal_norm_le
    (E := E) (F := fun _ : H => IntervalL1 𝕜) (p := 1) J 1 zero_le_one hj
  have hU : ‖U‖ ≤ 1 := lpFamilyDiagonal_norm_le
    (E := fun _ : H => IntervalL1 𝕜) (F := E) (p := 1) R 1 zero_le_one hr
  refine ⟨H, fun i => B i.val, hH, fun i => hB i.val, fun i => hp i.val,
    V, U, D, hV, hU,
    hUV, ⟨G, fun _ _ => rfl⟩, ?_⟩
  change ‖S - D‖ ≤ ε
  apply family_column_norm_le _ hε.le
  intro i x
  let Q := lpCoordinateProjection (𝕜 := 𝕜) (X := IntervalL1 𝕜) 1 (↑(F i.val) : Set Λ)ᶜ
  let P := lpCoordinateProjection (𝕜 := 𝕜) (X := IntervalL1 𝕜) 1 ({i.val} : Set Λ)ᶜ
  let w := T (lp.single 1 i.val (J i x))
  have hv : V (lp.single 1 i x) = lp.single 1 i (J i x) := by
    apply lp.ext
    funext k
    change J k (lp.single (E := E) 1 i x k) =
      lp.single (E := fun _ : H => IntervalL1 𝕜) 1 i (J i x) k
    by_cases hk : k = i
    · subst k; simp
    · rw [lp.single_apply_ne (E := E) _ _ _ hk,
        lp.single_apply_ne (E := fun _ : H => IntervalL1 𝕜) _ _ _ hk, map_zero]
  have hw : S (lp.single 1 i x) = U (keep w) := by
    change U (keep (T (insertH (V (lp.single 1 i x))))) = _
    rw [hv]
    have hi : insertH (lp.single 1 i (J i x)) = lp.single 1 i.val (J i x) :=
      extend_single (𝕜 := 𝕜) (Function.Embedding.subtype H) i (J i x)
    rw [hi]
  have heq : (S - D) (lp.single 1 i x) = U (keep (P (Q w))) := by
    apply lp.ext
    funext k
    by_cases hk : k = i
    · subst k
      change S (lp.single (E := E) 1 i x) i - G i (lp.single (E := E) 1 i x i) =
        R i (P (Q w) i.val)
      rw [lp.single_apply_self, show G i x = S (lp.single 1 i x) i from rfl, sub_self]
      simp [P]
    · have hk' : k.val ≠ i.val := fun h => hk (Subtype.ext h)
      have hf : k.val ∉ (↑(F i.val) : Set Λ) :=
        (hfree k.val k.property i.val i.property hk').1
      rw [ContinuousLinearMap.sub_apply, hw]
      change R k (w k.val) - G k (lp.single (E := E) 1 i x k) = R k (P (Q w) k.val)
      simp [P, Q, hk, hk', hf, lp.single_apply_ne]
  rw [heq]
  let W := U.comp (keep.comp P)
  have hnW : ‖W‖ ≤ 1 := by
    apply (norm_comp_right_contraction _ _ ?_).trans hU
    have hP : ‖P‖ ≤ 1 := norm_lpCoordinateProjection_le 1 _
    have hkeep : ‖keep‖ ≤ 1 := norm_lpRestrict_le (Function.Embedding.subtype H)
    exact (norm_comp_right_contraction keep P hP).trans hkeep
  have hnQ : ‖Q w‖ ≤ ε * ‖x‖ :=
    ((Q.comp ((col i.val).comp (J i))).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hc i.val).le (norm_nonneg x))
  exact ((W.le_opNorm (Q w)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnW (norm_nonneg (Q w)))).trans hnQ

/-- Lemma 6.5 over the real field. -/
theorem lemma_6_5_real (hΛ : Cardinal.aleph0 < Cardinal.mk Λ)
    (T : EllOneSum Λ (IntervalL1 ℝ) →L[ℝ] EllOneSum Λ (IntervalL1 ℝ)) {ε : ℝ}
    (hε : 0 < ε) : DiagonalReductionConclusion T ε :=
  localized_diagonal hΛ T hε (fun S => lemma_6_3_real S hε)

/-- Lemma 6.5 over the complex field. -/
theorem lemma_6_5_complex (hΛ : Cardinal.aleph0 < Cardinal.mk Λ)
    (T : EllOneSum Λ (IntervalL1 ℂ) →L[ℂ] EllOneSum Λ (IntervalL1 ℂ)) {ε : ℝ}
    (hε : 0 < ε) : DiagonalReductionConclusion T ε :=
  localized_diagonal hΛ T hε (fun S => lemma_6_3_complex S hε)

end UPFP.Printed
