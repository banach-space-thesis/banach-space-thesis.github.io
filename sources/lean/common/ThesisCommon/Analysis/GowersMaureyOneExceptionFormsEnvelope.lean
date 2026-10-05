import ThesisCommon.Analysis.GowersMaureyFormsEnvelope
import ThesisCommon.Analysis.GowersMaureySpreadProperness

/-! A norming envelope with one exceptional special length. The exceptional
tests retain their original coded special sequence and allow every actual
spread before interval restriction. Thus spread closure uses the proved
composition law and does not assert that spreading preserves the coding.
This is the norming step for the low-code absorption in source Lemma 8. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

inductive OneExceptionFormNormTest (D : ConstructionData 𝕜) (g : ℕ → ℝ) (k : ℕ) :
    Seminorm 𝕜 (C00 𝕜) → Prop
  | ordinary {p : Seminorm 𝕜 (C00 𝕜)} (hp : FormNormTest D g p) :
      OneExceptionFormNormTest D g k p
  | exceptional (hk : k ∈ D.specialSizes) (z : Fin k → C00 𝕜)
      (hz : SpecialSequence D (implicitNorm D) z) (m n : ℕ) (E : Interval) :
      OneExceptionFormNormTest D g k
        (((evaluationSeminorm (specialFunctional z)).comp (restrict E)).comp (spread m n))

theorem oneExceptionFormNormTests_nonempty (D : ConstructionData 𝕜) (g : ℕ → ℝ) (k : ℕ) :
    {p | OneExceptionFormNormTest D g k p}.Nonempty :=
  ⟨_, OneExceptionFormNormTest.ordinary (FormNormTest.coordinate 0)⟩

theorem oneExceptionFormNormTest_le_implicitNorm (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) {p : Seminorm 𝕜 (C00 𝕜)}
    (hp : OneExceptionFormNormTest D g k p) : p ≤ implicitNorm D := by
  cases hp with
  | ordinary hp => exact formNormTest_le_implicitNorm D g hp
  | exceptional hk z hz m n E =>
    intro x
    change ‖pairing (specialFunctional z) (restrict E (spread m n x))‖ ≤ _
    exact ((hz.specialFunctional_dualUnit D hk) _).trans
      ((implicitNorm_restrict_le D E (spread m n x)).trans
        (implicitNorm_spread_le D m n x))

theorem oneExceptionFormNormTests_bddAbove (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) : BddAbove {p | OneExceptionFormNormTest D g k p} :=
  ⟨implicitNorm D, fun _ hp => oneExceptionFormNormTest_le_implicitNorm D g k hp⟩

def oneExceptionFormNormEnvelope (D : ConstructionData 𝕜) (g : ℕ → ℝ) (k : ℕ) :
    Seminorm 𝕜 (C00 𝕜) := sSup {p | OneExceptionFormNormTest D g k p}

theorem oneExceptionFormNormEnvelope_le_implicitNorm (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) : oneExceptionFormNormEnvelope D g k ≤ implicitNorm D :=
  csSup_le (oneExceptionFormNormTests_nonempty D g k)
    (fun _ hp => oneExceptionFormNormTest_le_implicitNorm D g k hp)

theorem oneExceptionFormNormTest_le_envelope (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) {p : Seminorm 𝕜 (C00 𝕜)}
    (hp : OneExceptionFormNormTest D g k p) : p ≤ oneExceptionFormNormEnvelope D g k :=
  le_csSup (oneExceptionFormNormTests_bddAbove D g k) hp

theorem oneExceptionFormNormEnvelope_spread_le (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) (hgpos : ∀ l, 2 ≤ l → 0 < g l)
    (p q : ℕ) (x : C00 𝕜) :
    oneExceptionFormNormEnvelope D g k (spread p q x) ≤
      oneExceptionFormNormEnvelope D g k x := by
  rw [oneExceptionFormNormEnvelope,
    Seminorm.sSup_apply (oneExceptionFormNormTests_bddAbove D g k)]
  letI : Nonempty {s | OneExceptionFormNormTest D g k s} :=
    (oneExceptionFormNormTests_nonempty D g k).to_subtype
  apply ciSup_le
  rintro ⟨s, hs⟩
  cases hs with
  | ordinary hs =>
    cases hs with
    | coordinate i =>
      change ‖spread p q x i‖ ≤ _
      rw [spread_apply]
      split_ifs
      · exact oneExceptionFormNormTest_le_envelope D g k
          (OneExceptionFormNormTest.ordinary (FormNormTest.coordinate _)) x
      · simpa only [norm_zero] using apply_nonneg (oneExceptionFormNormEnvelope D g k) x
    | form hl a ha =>
      change ‖pairing a (spread p q x)‖ ≤ _
      rw [← pairing_spread_left]
      exact oneExceptionFormNormTest_le_envelope D g k
        (OneExceptionFormNormTest.ordinary
          (FormNormTest.form hl _ (ha.spread (hgpos _ hl) q p))) x
  | exceptional hk z hz m n E =>
    change ‖pairing (specialFunctional z) (restrict E (spread m n (spread p q x)))‖ ≤ _
    have he := LinearMap.congr_fun (spread_comp (𝕜 := 𝕜) m n p q) x
    change spread m n (spread p q x) = _ at he
    rw [he]
    exact oneExceptionFormNormTest_le_envelope D g k
      (OneExceptionFormNormTest.exceptional hk z hz _ _ E) x

theorem implicitNorm_eq_oneExceptionFormNormEnvelope (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) (hgpos : ∀ l, 2 ≤ l → 0 < g l)
    (hgf : ∀ l, 2 ≤ l → g l ≤ logarithmicWeight l)
    (hgspecial : ∀ l, l ∈ D.specialSizes → l ≠ k →
      g l ≤ Real.sqrt (logarithmicWeight l)) :
    implicitNorm D = oneExceptionFormNormEnvelope D g k := by
  apply le_antisymm _ (oneExceptionFormNormEnvelope_le_implicitNorm D g k)
  apply implicitNorm_le_of_closed D
  intro p hp
  cases hp with
  | coordinate n =>
    exact oneExceptionFormNormTest_le_envelope D g k
      (OneExceptionFormNormTest.ordinary (FormNormTest.coordinate n))
  | average T =>
    intro x
    obtain ⟨a, ha, hn⟩ := exists_intervalAverage_norming_form D T x
    calc
      intervalAverage (oneExceptionFormNormEnvelope D g k) T x ≤
          intervalAverage (implicitNorm D) T x := intervalAverage_mono T
        (oneExceptionFormNormEnvelope_le_implicitNorm D g k) x
      _ = ‖pairing a x‖ := hn.symm
      _ ≤ oneExceptionFormNormEnvelope D g k x := oneExceptionFormNormTest_le_envelope D g k
        (OneExceptionFormNormTest.ordinary (FormNormTest.form T.count_ge_two a
          (ha.of_weight_le (hgpos _ T.count_ge_two) (hgf _ T.count_ge_two)))) x
  | @special l hl z hz E =>
    have hz' := specialSequence_mono D
      (oneExceptionFormNormEnvelope_le_implicitNorm D g k) hz
    by_cases he : l = k
    · subst l
      intro x
      have h := oneExceptionFormNormTest_le_envelope D g k
        (OneExceptionFormNormTest.exceptional hl z hz' 0 0 E) x
      have hx : spread 0 0 x = x := by ext i; simp [spread_apply]
      simpa only [Seminorm.comp_apply, hx] using h
    · have hli := D.specialSize_ge_two hl
      have ha := (hz'.isForm D hl).of_weight_le (hgpos _ hli) (hgspecial _ hl he)
      intro x
      change ‖pairing (specialFunctional z) (restrict E x)‖ ≤ _
      rw [← pairing_restrict_left]
      exact oneExceptionFormNormTest_le_envelope D g k
        (OneExceptionFormNormTest.ordinary
          (FormNormTest.form hli _ (ha.restrict (hgpos _ hli) E))) x
  | spread m n => exact oneExceptionFormNormEnvelope_spread_le D g k hgpos m n

theorem exists_norming_form_of_one_exception_bound (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) (hgpos : ∀ l, 2 ≤ l → 0 < g l)
    (hgf : ∀ l, 2 ≤ l → g l ≤ logarithmicWeight l)
    (hgspecial : ∀ l, l ∈ D.specialSizes → l ≠ k →
      g l ≤ Real.sqrt (logarithmicWeight l))
    (x : C00 𝕜) {r b : ℝ} (hc : ∀ n, ‖x n‖ ≤ r)
    (hr : r < implicitNorm D x) (hb : b < implicitNorm D x)
    (hexception : ∀ z : Fin k → C00 𝕜, SpecialSequence D (implicitNorm D) z →
      ∀ m n E, ‖pairing (specialFunctional z) (restrict E (spread m n x))‖ ≤ b) :
    ∃ l : ℕ, 2 ≤ l ∧ ∃ a : C00 𝕜, IsForm D l (g l) a ∧ r < ‖pairing a x‖ := by
  by_contra h
  have hbound : oneExceptionFormNormEnvelope D g k x ≤ max r b := by
    rw [oneExceptionFormNormEnvelope,
      Seminorm.sSup_apply (oneExceptionFormNormTests_bddAbove D g k)]
    letI : Nonempty {p | OneExceptionFormNormTest D g k p} :=
      (oneExceptionFormNormTests_nonempty D g k).to_subtype
    apply ciSup_le
    rintro ⟨p, hp⟩
    cases hp with
    | ordinary hp =>
      cases hp with
      | coordinate n => exact (hc n).trans (le_max_left r b)
      | form hl a ha =>
        exact (le_of_not_gt (fun hlt => h ⟨_, hl, a, ha, hlt⟩)).trans (le_max_left r b)
    | exceptional hk z hz m n E => exact (hexception z hz m n E).trans (le_max_right r b)
  rw [← implicitNorm_eq_oneExceptionFormNormEnvelope D g k hgpos hgf hgspecial] at hbound
  exact (not_lt_of_ge hbound) (max_lt hr hb)

theorem affine_exception_bound_lt_norm {N B θ : ℝ}
    (hN : 1 < N) (hθ : θ < 1) (hB : B < 1 - θ) : B + θ * N < N := by
  have hprod : 0 < (1 - θ) * (N - 1) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem exists_norming_form_of_affine_exception_bound (D : ConstructionData 𝕜)
    (g : ℕ → ℝ) (k : ℕ) (hgpos : ∀ l, 2 ≤ l → 0 < g l)
    (hgf : ∀ l, 2 ≤ l → g l ≤ logarithmicWeight l)
    (hgspecial : ∀ l, l ∈ D.specialSizes → l ≠ k →
      g l ≤ Real.sqrt (logarithmicWeight l))
    (x : C00 𝕜) {r B θ : ℝ} (hc : ∀ n, ‖x n‖ ≤ r)
    (hr : r < implicitNorm D x) (hN : 1 < implicitNorm D x)
    (hθ : θ < 1) (hB : B < 1 - θ)
    (hexception : ∀ z : Fin k → C00 𝕜, SpecialSequence D (implicitNorm D) z →
      ∀ m n E, ‖pairing (specialFunctional z) (restrict E (spread m n x))‖ ≤
        B + θ * implicitNorm D x) :
    ∃ l : ℕ, 2 ≤ l ∧ ∃ a : C00 𝕜, IsForm D l (g l) a ∧ r < ‖pairing a x‖ :=
  exists_norming_form_of_one_exception_bound D g k hgpos hgf hgspecial x hc hr
    (affine_exception_bound_lt_norm hN hθ hB) hexception

end ThesisCommon.GowersMaurey
