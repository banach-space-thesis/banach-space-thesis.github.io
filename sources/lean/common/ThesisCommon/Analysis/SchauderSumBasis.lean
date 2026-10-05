import ThesisCommon.Analysis.SchauderSumOperators
import ThesisCommon.Analysis.SchauderCriterion

/-! The actual product basis of X(Y), with an arbitrary bijective ordering
of pairs of natural indices. Finite projection estimates and norm-density
give the full Schauder expansion, rather than assuming it as input.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}
variable (c : NormalizedSchauderBasis 𝕜 Y)

/-- Product vectors in the genuine sequence space. -/
def productVector (t : ℕ × ℕ) : SchauderSum b hb Y := single t.1 (c.vector t.2)

/-- Bounded scalar evaluation on a product coordinate. -/
def productCoordinate (t : ℕ × ℕ) : SchauderSum b hb Y →L[𝕜] 𝕜 :=
  (c.coord t.2).comp (coordinate (b := b) (hb := hb) (Y := Y) t.1)

theorem product_biorthogonal (i j : ℕ × ℕ) :
    productCoordinate (b := b) (hb := hb) c i (productVector c j) =
      if i = j then 1 else 0 := by
  classical
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  by_cases hij : i = j
  · subst j
    simp [productCoordinate, productVector, c.biorthogonal]
  · simp [productCoordinate, productVector, hij]

theorem productVector_norm (i : ℕ × ℕ) :
    ‖productVector (b := b) (hb := hb) c i‖ = 1 := by
  simp [productVector, c.norm_vector]

/-- The coefficient of a finite product expansion is its prescribed scalar. -/
theorem product_coord_finite_sum (e : ℕ ≃ ℕ × ℕ) (F : Finset ℕ)
    (a : ℕ → 𝕜) (t : ℕ × ℕ) :
    productCoordinate (b := b) (hb := hb) c t
      (∑ n ∈ F, a n • productVector c (e n)) =
      if e.symm t ∈ F then a (e.symm t) else 0 := by
  classical
  simp only [map_sum, map_smul, product_biorthogonal, smul_eq_mul]
  have heq (n : ℕ) : t = e n ↔ e.symm t = n := by
    constructor
    · intro h; rw [h, e.symm_apply_apply]
    · intro h; rw [← h, e.apply_symm_apply]
  simp [heq, Finset.sum_ite_eq]

theorem product_finite_projection_norm_le (hc : c.IsOneUnconditional)
    (e : ℕ ≃ ℕ × ℕ) (F : Finset ℕ) (y : SchauderSum b hb Y) :
    ‖∑ n ∈ F, productCoordinate c (e n) y •
      productVector (b := b) (hb := hb) c (e n)‖ ≤ ‖y‖ := by
  apply norm_le_of_apply_le
  intro i
  apply c.norm_le_of_coord_le hc
  intro j
  change ‖productCoordinate c (i, j)
    (∑ n ∈ F, productCoordinate c (e n) y • productVector c (e n))‖ ≤
      ‖productCoordinate c (i, j) y‖
  rw [product_coord_finite_sum]
  split_ifs
  · rw [e.apply_symm_apply]
  · simpa only [norm_zero] using norm_nonneg (productCoordinate c (i, j) y)

/-- Every vector is a norm limit of finite linear combinations of the
product vectors, by the inner and outer Schauder expansions. -/
theorem product_dense_span (e : ℕ ≃ ℕ × ℕ) :
    DenseRange (Submodule.span 𝕜
      (Set.range (fun n => productVector (b := b) (hb := hb) c (e n)))).subtypeL := by
  let S := Submodule.span 𝕜
    (Set.range (fun n => productVector (b := b) (hb := hb) c (e n)))
  have hs (i : ℕ) (z : Y) : single (b := b) (hb := hb) i z ∈ S.topologicalClosure := by
    have ht := ((singleL (b := b) (hb := hb) (Y := Y) i).continuous.tendsto z).comp
      (c.expansion z)
    apply S.isClosed_topologicalClosure.mem_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro N
    change singleL (b := b) (hb := hb) (Y := Y) i
      (∑ j ∈ Finset.range N, c.coord j z • c.vector j) ∈ S.topologicalClosure
    rw [map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul]
    apply Submodule.smul_mem
    apply S.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨e.symm (i, j), ?_⟩
    simp only [e.apply_symm_apply, productVector, singleL_apply]
  intro y
  have hy : y ∈ S.topologicalClosure := by
    apply S.isClosed_topologicalClosure.mem_of_tendsto (expansion y)
    apply Filter.Eventually.of_forall
    intro N
    exact Submodule.sum_mem _ (fun i _ => hs i (y i))
  change y ∈ closure (Set.range (Subtype.val : S → SchauderSum b hb Y))
  have hr : Set.range (Subtype.val : S → SchauderSum b hb Y) = (S : Set _) := by
    ext z
    exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  rw [hr]
  exact hy

/-- Any bijective ordering of pairs gives the actual product Schauder basis. -/
def productBasis (hc : c.IsOneUnconditional) (e : ℕ ≃ ℕ × ℕ) :
    NormalizedSchauderBasis 𝕜 (SchauderSum b hb Y) :=
  schauderBasisOfDenseSpan
    (fun n => productVector c (e n)) (fun n => productCoordinate c (e n))
    (fun i j => by rw [product_biorthogonal]; simp only [e.injective.eq_iff])
    (fun n => productVector_norm c (e n)) (product_dense_span c e)
    (product_finite_projection_norm_le c hc e)

/-- The product norm is one-unconditional under this enumeration. -/
theorem productBasis_oneUnconditional (hc : c.IsOneUnconditional) (e : ℕ ≃ ℕ × ℕ) :
    (productBasis (b := b) (hb := hb) c hc e).IsOneUnconditional := by
  classical
  refine ⟨le_rfl, ?_⟩
  intro F a d had
  rw [one_mul]
  change ‖∑ n ∈ F, a n • productVector c (e n)‖ ≤
    ‖∑ n ∈ F, d n • productVector (b := b) (hb := hb) c (e n)‖
  apply norm_le_of_apply_le
  intro i
  apply c.norm_le_of_coord_le hc
  intro j
  change ‖productCoordinate c (i, j) (∑ n ∈ F, a n • productVector c (e n))‖ ≤
    ‖productCoordinate c (i, j)
      (∑ n ∈ F, d n • productVector (b := b) (hb := hb) c (e n))‖
  rw [product_coord_finite_sum, product_coord_finite_sum]
  split_ifs with h
  · exact had _ h
  · exact le_rfl

end SchauderSum
end ThesisCommon
