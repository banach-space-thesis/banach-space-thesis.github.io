import ThesisCommon.Analysis.ComplexL1Complexification
import ThesisCommon.Analysis.OperatorModulusSup

/-! The genuine positive-decomposition supremum for operators from real L1
to complex L1. The sharp bound comes from additivity of the source L1 norm. -/
noncomputable section
open MeasureTheory Set Filter Topology Finset
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem complexL1Modulus_zero : complexL1Modulus (0 : Lp ℂ 1 ν) = 0 := by
  apply norm_eq_zero.mp
  rw [norm_complexL1Modulus, norm_zero]

theorem complexL1Modulus_sum_le {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 1 ν) :
    complexL1Modulus (∑ i ∈ s, f i) ≤ ∑ i ∈ s, complexL1Modulus (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexL1Modulus_zero]
  | @insert i s his ih =>
    rw [sum_insert his, sum_insert his]
    exact (complexL1Modulus_add_le _ _).trans (add_le_add_left ih _)

namespace PositiveDecomposition
def complexValue (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) {x : Lp ℝ 1 μ}
    (d : PositiveDecomposition x) : Lp ℝ 1 ν := ∑ i, complexL1Modulus (T (d.part i))

theorem complexValue_nonneg (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) {x : Lp ℝ 1 μ}
    (d : PositiveDecomposition x) : 0 ≤ d.complexValue T :=
  sum_nonneg fun _ _ => complexL1Modulus_nonneg _

theorem complexValue_single (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) (x : Lp ℝ 1 μ) (hx : 0 ≤ x) :
    (single x hx).complexValue T = complexL1Modulus (T x) := by simp [complexValue, single]

theorem complexValue_append (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) {x y : Lp ℝ 1 μ}
    (d : PositiveDecomposition x) (e : PositiveDecomposition y) :
    (d.append e).complexValue T = d.complexValue T + e.complexValue T := by
  simp [complexValue, append, Fintype.sum_sum_type]

theorem exists_split_complexValue (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    {x y : Lp ℝ 1 μ} (hx : 0 ≤ x) (hy : 0 ≤ y) (d : PositiveDecomposition (x+y)) :
    ∃ a : PositiveDecomposition x, ∃ b : PositiveDecomposition y,
      d.complexValue T ≤ a.complexValue T + b.complexValue T := by
  obtain ⟨u,hu,husum⟩ := riesz_split_finset univ d.part (fun i _ => d.nonneg i) x hx
    (by rw [d.sum_eq]; exact le_add_of_nonneg_right hy)
  let a : PositiveDecomposition x :=
    { Index := d.Index
      part := u
      nonneg := fun i => (hu i (mem_univ _)).1
      sum_eq := husum }
  let b : PositiveDecomposition y :=
    { Index := d.Index
      part := fun i => d.part i-u i
      nonneg := fun i => sub_nonneg.mpr (hu i (mem_univ _)).2
      sum_eq := by rw [sum_sub_distrib, d.sum_eq, husum]; abel }
  refine ⟨a,b,?_⟩
  change (∑ i, complexL1Modulus (T (d.part i))) ≤
    (∑ i, complexL1Modulus (T (u i))) + ∑ i, complexL1Modulus (T (d.part i-u i))
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i _
  have he : d.part i = u i + (d.part i-u i) := by abel
  conv_lhs => rw [he, map_add]
  exact complexL1Modulus_add_le _ _

theorem exists_complexValue_ge_pair (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    {x : Lp ℝ 1 μ} (d e : PositiveDecomposition x) :
    ∃ q : PositiveDecomposition x,
      d.complexValue T ≤ q.complexValue T ∧ e.complexValue T ≤ q.complexValue T := by
  obtain ⟨c,hc,hr,hcol⟩ := riesz_refine_finsets univ univ d.part e.part
    (fun i _ => d.nonneg i) (fun i _ => e.nonneg i) (d.sum_eq.trans e.sum_eq.symm)
  let q : PositiveDecomposition x :=
    { Index := d.Index × e.Index
      part := fun z => c z.1 z.2
      nonneg := fun z => hc z.1 (mem_univ _) z.2 (mem_univ _)
      sum_eq := by
        rw [Fintype.sum_prod_type]
        simp_rw [hr _ (mem_univ _)]
        exact d.sum_eq }
  refine ⟨q,?_,?_⟩
  · calc
      d.complexValue T ≤ ∑ i, ∑ j, complexL1Modulus (T (c i j)) := by
        apply sum_le_sum
        intro i _
        rw [← hr i (mem_univ _), map_sum]
        exact complexL1Modulus_sum_le _ _
      _ = q.complexValue T := by simp only [complexValue,q,Fintype.sum_prod_type]
  · calc
      e.complexValue T ≤ ∑ j, ∑ i, complexL1Modulus (T (c i j)) := by
        apply sum_le_sum
        intro j _
        rw [← hcol j (mem_univ _), map_sum]
        exact complexL1Modulus_sum_le _ _
      _ = q.complexValue T := by rw [sum_comm]; simp only [complexValue,q,Fintype.sum_prod_type]

theorem norm_complexValue_le (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    {x : Lp ℝ 1 μ} (d : PositiveDecomposition x) : ‖d.complexValue T‖ ≤ ‖T‖*‖x‖ := by
  calc
    ‖d.complexValue T‖ ≤ ∑ i, ‖complexL1Modulus (T (d.part i))‖ := norm_sum_le _ _
    _ = ∑ i, ‖T (d.part i)‖ := by simp only [norm_complexL1Modulus]
    _ ≤ ∑ i, ‖T‖*‖d.part i‖ := sum_le_sum fun i _ => T.le_opNorm _
    _ = ‖T‖*‖x‖ := by
      rw [← mul_sum, ← al_norm_sum (lOne_norm_add_of_nonneg μ) univ d.part
        (fun i _ => d.nonneg i), d.sum_eq]
end PositiveDecomposition

def complexModulusCandidates (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) (x : Lp ℝ 1 μ) :
    Set (Lp ℝ 1 ν) := range (fun d : PositiveDecomposition x => d.complexValue T)

theorem exists_complexOperatorModulus_value (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) :
    ∃ y : Lp ℝ 1 ν, IsLUB (complexModulusCandidates T x) y ∧
      0 ≤ y ∧ ‖y‖ ≤ ‖T‖*‖x‖ := by
  have hne : (complexModulusCandidates T x).Nonempty :=
    ⟨(PositiveDecomposition.single x hx).complexValue T, ⟨_,rfl⟩⟩
  have hpos : ∀ z ∈ complexModulusCandidates T x, 0 ≤ z := by
    rintro _ ⟨d,rfl⟩
    exact d.complexValue_nonneg T
  have hdir : DirectedOn (· ≤ ·) (complexModulusCandidates T x) := by
    rintro _ ⟨d,rfl⟩ _ ⟨e,rfl⟩
    obtain ⟨q,hd,he⟩ := d.exists_complexValue_ge_pair T e
    exact ⟨q.complexValue T,⟨q,rfl⟩,hd,he⟩
  have hbdd : BddAbove (norm '' complexModulusCandidates T x) := by
    refine ⟨‖T‖*‖x‖,?_⟩
    rintro _ ⟨_,⟨d,rfl⟩,rfl⟩
    exact d.norm_complexValue_le T
  obtain ⟨y,hlub,u,hu,hulim,_⟩ := al_exists_isLUB_of_directed_norm_bdd
    (lOne_norm_add_of_nonneg ν) hne hpos hdir hbdd
  refine ⟨y,hlub,?_,?_⟩
  · obtain ⟨z,hz⟩ := hne
    exact (hpos z hz).trans (hlub.1 hz)
  · apply le_of_tendsto' hulim.norm
    intro n
    obtain ⟨d,hd⟩ := hu n
    rw [← hd]
    exact d.norm_complexValue_le T

def complexOperatorModulusPos (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : Lp ℝ 1 ν :=
  (exists_complexOperatorModulus_value T x hx).choose

theorem complexOperatorModulusPos_isLUB (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) :
    IsLUB (complexModulusCandidates T x) (complexOperatorModulusPos T x hx) :=
  (exists_complexOperatorModulus_value T x hx).choose_spec.1

theorem complexOperatorModulusPos_nonneg (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : 0 ≤ complexOperatorModulusPos T x hx :=
  (exists_complexOperatorModulus_value T x hx).choose_spec.2.1

theorem norm_complexOperatorModulusPos_le (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : ‖complexOperatorModulusPos T x hx‖ ≤ ‖T‖*‖x‖ :=
  (exists_complexOperatorModulus_value T x hx).choose_spec.2.2

theorem complexOperatorModulusPos_zero (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν) :
    complexOperatorModulusPos T 0 (le_refl 0) = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using norm_complexOperatorModulusPos_le T 0 (le_refl 0)) (norm_nonneg _)

theorem complexOperatorModulusPos_dominates (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x : Lp ℝ 1 μ) (hx : 0 ≤ x) : complexL1Modulus (T x) ≤ complexOperatorModulusPos T x hx := by
  have h := (complexOperatorModulusPos_isLUB T x hx).1
    (show (PositiveDecomposition.single x hx).complexValue T ∈ complexModulusCandidates T x from ⟨_,rfl⟩)
  simpa [PositiveDecomposition.complexValue_single] using h

theorem complexOperatorModulusPos_add (T : Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν)
    (x y : Lp ℝ 1 μ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    complexOperatorModulusPos T (x+y) (add_nonneg hx hy) =
      complexOperatorModulusPos T x hx + complexOperatorModulusPos T y hy := by
  let M := complexOperatorModulusPos T
  have hmx := complexOperatorModulusPos_isLUB T x hx
  have hmy := complexOperatorModulusPos_isLUB T y hy
  have hmxy := complexOperatorModulusPos_isLUB T (x+y) (add_nonneg hx hy)
  apply le_antisymm
  · apply hmxy.2
    rintro _ ⟨d,rfl⟩
    obtain ⟨a,b,hd⟩ := d.exists_split_complexValue T hx hy
    exact hd.trans (add_le_add (hmx.1 ⟨a,rfl⟩) (hmy.1 ⟨b,rfl⟩))
  · have hinner (b : PositiveDecomposition y) :
        M x hx + b.complexValue T ≤ M (x+y) (add_nonneg hx hy) := by
      apply le_sub_iff_add_le.mp
      apply hmx.2
      rintro _ ⟨a,rfl⟩
      apply le_sub_iff_add_le.mpr
      have h := hmxy.1 (show (a.append b).complexValue T ∈ complexModulusCandidates T (x+y) from ⟨_,rfl⟩)
      rwa [PositiveDecomposition.complexValue_append] at h
    apply le_sub_iff_add_le'.mp
    apply hmy.2
    rintro _ ⟨b,rfl⟩
    exact le_sub_iff_add_le'.mpr (hinner b)

end ThesisCommon
