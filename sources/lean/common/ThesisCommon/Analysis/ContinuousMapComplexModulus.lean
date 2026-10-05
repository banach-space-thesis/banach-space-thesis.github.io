import ThesisCommon.Analysis.ContinuousMapComplexPositiveBound

/-! The scalar Riesz–Kantorovich modulus of an actual complex functional
on C(K). Unit phases of finite positive decompositions give the sharp norm
bound; the resulting positive functional is constructed by cone extension. -/
noncomputable section
open Set Finset
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

def continuousMapComplexDecompositionValue (φ : C(K, ℂ) →L[ℂ] ℂ)
    {f : C(K, ℝ)} (d : PositiveDecomposition f) : ℝ :=
  ∑ i, ‖φ (continuousMapOfReal (d.part i))‖

theorem continuousMapComplexDecompositionValue_nonneg (φ : C(K, ℂ) →L[ℂ] ℂ)
    {f : C(K, ℝ)} (d : PositiveDecomposition f) :
    0 ≤ continuousMapComplexDecompositionValue φ d := sum_nonneg fun _ _ => norm_nonneg _

theorem continuousMapComplexDecompositionValue_le (φ : C(K, ℂ) →L[ℂ] ℂ)
    {f : C(K, ℝ)} (d : PositiveDecomposition f) :
    continuousMapComplexDecompositionValue φ d ≤ ‖φ‖ * ‖f‖ := by
  classical
  choose c hc he using fun i : d.Index => Complex.exists_norm_eq_mul_self (φ (continuousMapOfReal (d.part i)))
  let F : C(K, ℂ) := ∑ i, c i • continuousMapOfReal (d.part i)
  have hFnorm : ‖F‖ ≤ ‖f‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro t
    calc
      ‖F t‖ = ‖∑ i, c i * ((d.part i t : ℝ) : ℂ)‖ := by simp [F, smul_eq_mul]
      _ ≤ ∑ i, ‖c i * ((d.part i t : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ i, d.part i t := by
        apply sum_congr rfl
        intro i hi
        rw [norm_mul, hc, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (d.nonneg i t)]
      _ = f t := by simpa using congrArg (fun g : C(K, ℝ) => g t) d.sum_eq
      _ ≤ ‖f‖ := (le_abs_self _).trans (f.norm_coe_le_norm t)
  have heval : continuousMapComplexDecompositionValue φ d = (φ F).re := by
    simp only [continuousMapComplexDecompositionValue, F, map_sum, map_smul,
      Complex.re_sum, smul_eq_mul]
    apply sum_congr rfl
    intro i hi
    rw [← he i]
    rfl
  calc
    continuousMapComplexDecompositionValue φ d = (φ F).re := heval
    _ ≤ ‖φ F‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ ≤ ‖φ‖ * ‖F‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * ‖f‖ := mul_le_mul_of_nonneg_left hFnorm (norm_nonneg φ)

theorem continuousMapComplexDecompositionValue_single (φ : C(K, ℂ) →L[ℂ] ℂ)
    (f : C(K, ℝ)) (hf : 0 ≤ f) :
    continuousMapComplexDecompositionValue φ (PositiveDecomposition.single f hf) =
      ‖φ (continuousMapOfReal f)‖ := by
  simp [continuousMapComplexDecompositionValue, PositiveDecomposition.single]

theorem continuousMapComplexDecompositionValue_append (φ : C(K, ℂ) →L[ℂ] ℂ)
    {f g : C(K, ℝ)} (d : PositiveDecomposition f) (e : PositiveDecomposition g) :
    continuousMapComplexDecompositionValue φ (d.append e) =
      continuousMapComplexDecompositionValue φ d + continuousMapComplexDecompositionValue φ e := by
  simp [continuousMapComplexDecompositionValue, PositiveDecomposition.append, Fintype.sum_sum_type]

theorem exists_split_continuousMapComplexDecompositionValue (φ : C(K, ℂ) →L[ℂ] ℂ)
    {f g : C(K, ℝ)} (hf : 0 ≤ f) (hg : 0 ≤ g) (d : PositiveDecomposition (f + g)) :
    ∃ a : PositiveDecomposition f, ∃ b : PositiveDecomposition g,
      continuousMapComplexDecompositionValue φ d ≤
        continuousMapComplexDecompositionValue φ a + continuousMapComplexDecompositionValue φ b := by
  obtain ⟨u, hu, husum⟩ := riesz_split_finset univ d.part (fun i _ => d.nonneg i) f hf
    (by rw [d.sum_eq]; exact le_add_of_nonneg_right hg)
  let a : PositiveDecomposition f :=
    { Index := d.Index
      part := u
      nonneg := fun i => (hu i (mem_univ _)).1
      sum_eq := husum }
  let b : PositiveDecomposition g :=
    { Index := d.Index
      part := fun i => d.part i - u i
      nonneg := fun i => sub_nonneg.mpr (hu i (mem_univ _)).2
      sum_eq := by rw [sum_sub_distrib, d.sum_eq, husum]; abel }
  refine ⟨a, b, ?_⟩
  change (∑ i, ‖φ (continuousMapOfReal (d.part i))‖) ≤
    (∑ i, ‖φ (continuousMapOfReal (u i))‖) + ∑ i, ‖φ (continuousMapOfReal (d.part i - u i))‖
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  have he : d.part i = u i + (d.part i - u i) := by abel
  conv_lhs => rw [he, map_add, map_add]
  exact norm_add_le _ _

def continuousMapComplexModulusPos (φ : C(K, ℂ) →L[ℂ] ℂ) (f : C(K, ℝ)) (_hf : 0 ≤ f) : ℝ :=
  sSup (range (fun d : PositiveDecomposition f => continuousMapComplexDecompositionValue φ d))

theorem continuousMapComplexModulusPos_isLUB (φ : C(K, ℂ) →L[ℂ] ℂ) (f : C(K, ℝ)) (hf : 0 ≤ f) :
    IsLUB (range (fun d : PositiveDecomposition f => continuousMapComplexDecompositionValue φ d))
      (continuousMapComplexModulusPos φ f hf) := by
  apply isLUB_csSup
  · exact ⟨_, ⟨PositiveDecomposition.single f hf, rfl⟩⟩
  · refine ⟨‖φ‖ * ‖f‖, ?_⟩
    rintro _ ⟨d, rfl⟩
    exact continuousMapComplexDecompositionValue_le φ d

theorem continuousMapComplexModulusPos_dominates (φ : C(K, ℂ) →L[ℂ] ℂ)
    (f : C(K, ℝ)) (hf : 0 ≤ f) : ‖φ (continuousMapOfReal f)‖ ≤ continuousMapComplexModulusPos φ f hf := by
  simpa only [continuousMapComplexDecompositionValue_single] using
    (continuousMapComplexModulusPos_isLUB φ f hf).1 ⟨PositiveDecomposition.single f hf, rfl⟩

theorem continuousMapComplexModulusPos_nonneg (φ : C(K, ℂ) →L[ℂ] ℂ)
    (f : C(K, ℝ)) (hf : 0 ≤ f) : 0 ≤ continuousMapComplexModulusPos φ f hf :=
  (norm_nonneg _).trans (continuousMapComplexModulusPos_dominates φ f hf)

theorem continuousMapComplexModulusPos_le (φ : C(K, ℂ) →L[ℂ] ℂ)
    (f : C(K, ℝ)) (hf : 0 ≤ f) : continuousMapComplexModulusPos φ f hf ≤ ‖φ‖ * ‖f‖ := by
  apply (continuousMapComplexModulusPos_isLUB φ f hf).2
  rintro _ ⟨d, rfl⟩
  exact continuousMapComplexDecompositionValue_le φ d

theorem continuousMapComplexModulusPos_add (φ : C(K, ℂ) →L[ℂ] ℂ)
    (f g : C(K, ℝ)) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    continuousMapComplexModulusPos φ (f + g) (add_nonneg hf hg) =
      continuousMapComplexModulusPos φ f hf + continuousMapComplexModulusPos φ g hg := by
  have hmf := continuousMapComplexModulusPos_isLUB φ f hf
  have hmg := continuousMapComplexModulusPos_isLUB φ g hg
  have hmfg := continuousMapComplexModulusPos_isLUB φ (f + g) (add_nonneg hf hg)
  apply le_antisymm
  · apply hmfg.2
    rintro _ ⟨d, rfl⟩
    obtain ⟨a, b, hd⟩ := exists_split_continuousMapComplexDecompositionValue φ hf hg d
    exact hd.trans (add_le_add (hmf.1 ⟨a, rfl⟩) (hmg.1 ⟨b, rfl⟩))
  · have hinner (b : PositiveDecomposition g) :
        continuousMapComplexModulusPos φ f hf + continuousMapComplexDecompositionValue φ b ≤
          continuousMapComplexModulusPos φ (f + g) (add_nonneg hf hg) := by
      apply le_sub_iff_add_le.mp
      apply hmf.2
      rintro _ ⟨a, rfl⟩
      apply le_sub_iff_add_le.mpr
      simpa only [continuousMapComplexDecompositionValue_append] using hmfg.1 ⟨a.append b, rfl⟩
    apply le_sub_iff_add_le'.mp
    apply hmg.2
    rintro _ ⟨b, rfl⟩
    exact le_sub_iff_add_le'.mpr (hinner b)

def continuousMapComplexModulus (φ : C(K, ℂ) →L[ℂ] ℂ) : C(K, ℝ) →L[ℝ] ℝ :=
  positiveConeExtension (continuousMapComplexModulusPos φ) (continuousMapComplexModulusPos_add φ)
    (norm_nonneg φ) (fun f hf => by
      rw [Real.norm_eq_abs, abs_of_nonneg (continuousMapComplexModulusPos_nonneg φ f hf)]
      exact continuousMapComplexModulusPos_le φ f hf)

theorem continuousMapComplexModulus_apply_nonneg (φ : C(K, ℂ) →L[ℂ] ℂ)
    (f : C(K, ℝ)) (hf : 0 ≤ f) :
    continuousMapComplexModulus φ f = continuousMapComplexModulusPos φ f hf :=
  positiveConeExtension_apply_of_nonneg _ _ _ _ f hf

theorem continuousMapComplexModulus_nonneg (φ : C(K, ℂ) →L[ℂ] ℂ) : 0 ≤ continuousMapComplexModulus φ := by
  intro f hf
  change 0 ≤ continuousMapComplexModulus φ f
  rw [continuousMapComplexModulus_apply_nonneg φ f hf]
  exact continuousMapComplexModulusPos_nonneg φ f hf

theorem continuousMapComplexModulus_dominates (φ : C(K, ℂ) →L[ℂ] ℂ)
    (f : C(K, ℝ)) (hf : 0 ≤ f) : ‖φ (continuousMapOfReal f)‖ ≤ continuousMapComplexModulus φ f := by
  rw [continuousMapComplexModulus_apply_nonneg φ f hf]
  exact continuousMapComplexModulusPos_dominates φ f hf

theorem norm_continuousMapComplexModulus (φ : C(K, ℂ) →L[ℂ] ℂ) :
    ‖continuousMapComplexModulus φ‖ = ‖φ‖ := by
  have hpos := continuousMapComplexModulus_nonneg φ
  apply le_antisymm
  · rw [norm_positive_continuousMapDual _ hpos, continuousMapComplexModulus_apply_nonneg _ _
      (show 0 ≤ (1 : C(K, ℝ)) from fun _ => zero_le_one)]
    apply (continuousMapComplexModulusPos_le _ _ _).trans
    have hone : ‖(1 : C(K, ℝ))‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr (fun _ => by simp)
    simpa using mul_le_mul_of_nonneg_left hone (norm_nonneg φ)
  · rw [norm_positive_continuousMapDual _ hpos]
    exact norm_continuousMap_complex_functional_le_positive_bound φ _
      ((operator_nonneg_iff _).mp hpos) (continuousMapComplexModulus_dominates φ)

end ThesisCommon
