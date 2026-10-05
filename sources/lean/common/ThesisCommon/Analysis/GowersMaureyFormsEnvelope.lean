import ThesisCommon.Analysis.GowersMaureyAdjointSpreads
import ThesisCommon.Analysis.GowersMaureyNormMinimality

/-! The actual implicit norm is normed by coordinate tests and genuine
forms whenever the numerical profile lies below f and below sqrt(f) at
the special sizes. The spread clause is handled by transposed spreads;
this norming description is proved from minimality, not assumed. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

inductive FormNormTest (D : ConstructionData 𝕜) (g : ℕ → ℝ) :
    Seminorm 𝕜 (C00 𝕜) → Prop
  | coordinate (n : ℕ) : FormNormTest D g (coordinateSeminorm n)
  | form {k : ℕ} (hk : 2 ≤ k) (a : C00 𝕜) (ha : IsForm D k (g k) a) :
      FormNormTest D g (evaluationSeminorm a)

theorem formNormTests_nonempty (D : ConstructionData 𝕜) (g : ℕ → ℝ) :
    {p | FormNormTest D g p}.Nonempty := ⟨_, FormNormTest.coordinate 0⟩

theorem formNormTest_le_implicitNorm (D : ConstructionData 𝕜) (g : ℕ → ℝ)
    {p : Seminorm 𝕜 (C00 𝕜)} (hp : FormNormTest D g p) : p ≤ implicitNorm D := by
  cases hp with
  | coordinate n => exact test_le_implicitNorm D (NormTest.coordinate n)
  | form hk a ha => exact ha.1

theorem formNormTests_bddAbove (D : ConstructionData 𝕜) (g : ℕ → ℝ) :
    BddAbove {p | FormNormTest D g p} :=
  ⟨implicitNorm D, fun _ hp => formNormTest_le_implicitNorm D g hp⟩

def formNormEnvelope (D : ConstructionData 𝕜) (g : ℕ → ℝ) : Seminorm 𝕜 (C00 𝕜) :=
  sSup {p | FormNormTest D g p}

theorem formNormEnvelope_le_implicitNorm (D : ConstructionData 𝕜) (g : ℕ → ℝ) :
    formNormEnvelope D g ≤ implicitNorm D :=
  csSup_le (formNormTests_nonempty D g) (fun _ hp => formNormTest_le_implicitNorm D g hp)

theorem formNormTest_le_envelope (D : ConstructionData 𝕜) (g : ℕ → ℝ)
    {p : Seminorm 𝕜 (C00 𝕜)} (hp : FormNormTest D g p) : p ≤ formNormEnvelope D g :=
  le_csSup (formNormTests_bddAbove D g) hp

theorem formNormEnvelope_spread_le (D : ConstructionData 𝕜) (g : ℕ → ℝ)
    (hgpos : ∀ k, 2 ≤ k → 0 < g k) (m n : ℕ) (x : C00 𝕜) :
    formNormEnvelope D g (spread m n x) ≤ formNormEnvelope D g x := by
  rw [formNormEnvelope, Seminorm.sSup_apply (formNormTests_bddAbove D g)]
  letI : Nonempty {p | FormNormTest D g p} := (formNormTests_nonempty D g).to_subtype
  apply ciSup_le
  intro p
  obtain ⟨p, hp⟩ := p
  cases hp with
  | coordinate i =>
    change ‖spread m n x i‖ ≤ _
    rw [spread_apply]
    split_ifs
    · exact formNormTest_le_envelope D g (FormNormTest.coordinate _) x
    · simpa only [norm_zero] using apply_nonneg (formNormEnvelope D g) x
  | form hk a ha =>
    change ‖pairing a (spread m n x)‖ ≤ _
    rw [← pairing_spread_left]
    exact formNormTest_le_envelope D g (FormNormTest.form hk _ (ha.spread (hgpos _ hk) n m)) x

theorem ConstructionData.specialSize_ge_two (D : ConstructionData 𝕜)
    {k : ℕ} (hk : k ∈ D.specialSizes) : 2 ≤ k := by
  obtain ⟨n, rfl⟩ := hk
  have hle : D.j 0 ≤ D.j (2 * n) := D.j_strict.monotone (Nat.zero_le _)
  have hpos := D.j_positive 0
  by_contra h
  change ¬ 2 ≤ D.j (2 * n) at h
  have hzero : D.j 0 = 1 := by omega
  have hb := D.first_large
  rw [hzero] at hb
  norm_num [logarithmicWeight_one] at hb

theorem implicitNorm_eq_formNormEnvelope (D : ConstructionData 𝕜) (g : ℕ → ℝ)
    (hgpos : ∀ k, 2 ≤ k → 0 < g k)
    (hgf : ∀ k, 2 ≤ k → g k ≤ logarithmicWeight k)
    (hgspecial : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k)) :
    implicitNorm D = formNormEnvelope D g := by
  apply le_antisymm _ (formNormEnvelope_le_implicitNorm D g)
  apply implicitNorm_le_of_closed D
  intro p hp
  cases hp with
  | coordinate n => exact formNormTest_le_envelope D g (FormNormTest.coordinate n)
  | average T =>
    intro x
    obtain ⟨a, ha, hn⟩ := exists_intervalAverage_norming_form D T x
    calc
      intervalAverage (formNormEnvelope D g) T x ≤ intervalAverage (implicitNorm D) T x :=
        intervalAverage_mono T (formNormEnvelope_le_implicitNorm D g) x
      _ = ‖pairing a x‖ := hn.symm
      _ ≤ formNormEnvelope D g x := formNormTest_le_envelope D g
        (FormNormTest.form T.count_ge_two a
          (ha.of_weight_le (hgpos _ T.count_ge_two) (hgf _ T.count_ge_two))) x
  | special hk z hz E =>
    have hki := D.specialSize_ge_two hk
    have hz' := specialSequence_mono D (formNormEnvelope_le_implicitNorm D g) hz
    have ha := (hz'.isForm D hk).of_weight_le (hgpos _ hki) (hgspecial _ hk)
    intro x
    change ‖pairing (specialFunctional z) (restrict E x)‖ ≤ _
    rw [← pairing_restrict_left]
    exact formNormTest_le_envelope D g (FormNormTest.form hki _ (ha.restrict (hgpos _ hki) E)) x
  | spread m n => exact formNormEnvelope_spread_le D g hgpos m n

theorem exists_norming_form_of_coordinate_bound (D : ConstructionData 𝕜) (g : ℕ → ℝ)
    (hgpos : ∀ k, 2 ≤ k → 0 < g k)
    (hgf : ∀ k, 2 ≤ k → g k ≤ logarithmicWeight k)
    (hgspecial : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k))
    (x : C00 𝕜) {r : ℝ} (hc : ∀ n, ‖x n‖ ≤ r) (hr : r < implicitNorm D x) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ a : C00 𝕜, IsForm D k (g k) a ∧ r < ‖pairing a x‖ := by
  by_contra h
  have hbound : formNormEnvelope D g x ≤ r := by
    rw [formNormEnvelope, Seminorm.sSup_apply (formNormTests_bddAbove D g)]
    letI : Nonempty {p | FormNormTest D g p} := (formNormTests_nonempty D g).to_subtype
    apply ciSup_le
    rintro ⟨p, hp⟩
    cases hp with
    | coordinate n => exact hc n
    | form hk a ha => exact le_of_not_gt (fun hlt => h ⟨_, hk, a, ha, hlt⟩)
  rw [← implicitNorm_eq_formNormEnvelope D g hgpos hgf hgspecial] at hbound
  exact (not_lt_of_ge hbound) hr

end ThesisCommon.GowersMaurey
