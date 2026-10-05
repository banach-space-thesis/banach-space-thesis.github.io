import ThesisCommon.Analysis.JamesTreeAntichainNorms
import ThesisCommon.Analysis.JamesTreeFiniteMasks

/-! Genuine finite ℓp antichain copies in each completed tree space, with
contractive coordinate reading and an actual complementary projection. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeAntichainInsert {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S) :
    PiLp p.val (fun _ : Fin n => 𝕜) →ₗᵢ[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  (jamesTreeDenseEmbedding 𝕜 p S).comp (JamesTreePreSpace.antichainInsertIsometry e he hS)

theorem jamesTreeAntichainInsert_apply {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S)
    (a : PiLp p.val (fun _ : Fin n => 𝕜)) :
    jamesTreeAntichainInsert e he hS a = ∑ i, a i • jamesTreeUnit (e i) := by
  change jamesTreeDenseEmbedding 𝕜 p S (∑ i, JamesTreePreSpace.single (e i) (a i)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => jamesTree_dense_smul_unit (e i) (a i))

theorem jamesTree_antichain_norm {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S)
    (a : Fin n → 𝕜) :
    ‖∑ i, a i • jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) (e i)‖ = ‖WithLp.toLp p.val a‖ := by
  calc
    _ = ‖jamesTreeAntichainInsert e he hS (WithLp.toLp p.val a)‖ :=
      congrArg norm (jamesTreeAntichainInsert_apply e he hS (WithLp.toLp p.val a)).symm
    _ = _ := (jamesTreeAntichainInsert e he hS).norm_map _

theorem jamesTree_antichain_norm_finite {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S)
    (hp : p.val ≠ ∞) (a : Fin n → 𝕜) :
    ‖∑ i, a i • jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) (e i)‖ =
      (∑ i, ‖a i‖ ^ p.val.toReal) ^ (1 / p.val.toReal) := by
  rw [jamesTree_antichain_norm e he hS a]
  exact PiLp.norm_eq_sum (ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le p.property)) hp) _

def jamesTreeFiniteRead {n : ℕ} (e : Fin n ↪ DyadicTreeNode) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] PiLp p.val (fun _ : Fin n => 𝕜) :=
  (PiLp.continuousLinearEquiv (𝕜 := 𝕜) p.val (fun _ : Fin n => 𝕜)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => jamesTreeCoordinate (e i)))

@[simp] theorem jamesTreeFiniteRead_apply {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) (i : Fin n) :
    jamesTreeFiniteRead e x i = jamesTreeCoordinate (e i) x := rfl

theorem jamesTreeFiniteRead_norm_le {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreeFiniteRead e x‖ ≤ ‖x‖ := by
  classical
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeFiniteRead e).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeDenseEmbedding_norm]
    have hread : jamesTreeFiniteRead e (jamesTreeDenseEmbedding 𝕜 p S a) =
        WithLp.toLp p.val (fun i => a (e i)) := by
      ext i
      exact jamesTreeCoordinate_dense (e i) a
    rw [hread]
    simpa only [Finset.sum_singleton] using
      jamesTree_partial_test_norm_le p a (fun i : Fin n => {e i})
        (fun i _ => S.singleton_allowed (e i))
        (fun i j hij => Finset.disjoint_singleton.mpr (e.injective.ne hij))

theorem norm_jamesTreeFiniteRead_le {n : ℕ} (e : Fin n ↪ DyadicTreeNode) :
    ‖jamesTreeFiniteRead (𝕜 := 𝕜) (p := p) (S := S) e‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa only [one_mul] using jamesTreeFiniteRead_norm_le e x)

theorem jamesTreeFiniteRead_comp_antichainInsert {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S) :
    (jamesTreeFiniteRead (𝕜 := 𝕜) (p := p) e).comp
      (jamesTreeAntichainInsert e he hS).toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro a
  ext i
  change jamesTreeCoordinate (e i)
    (jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.antichainInsertLinear e a)) = a i
  rw [jamesTreeCoordinate_dense, JamesTreePreSpace.antichainInsertLinear_apply_image]

def jamesTreeAntichainProjection {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  (jamesTreeAntichainInsert e he hS).toContinuousLinearMap.comp (jamesTreeFiniteRead e)

theorem norm_jamesTreeAntichainProjection_le {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S) :
    ‖jamesTreeAntichainProjection (𝕜 := 𝕜) (p := p) e he hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖jamesTreeAntichainInsert e he hS (jamesTreeFiniteRead e x)‖ ≤ 1 * ‖x‖
  rw [LinearIsometry.norm_map, one_mul]
  exact jamesTreeFiniteRead_norm_le e x

theorem jamesTreeAntichainProjection_idempotent {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hS : JamesTreeSegmentsAreChains S) :
    (jamesTreeAntichainProjection (𝕜 := 𝕜) (p := p) e he hS).comp
      (jamesTreeAntichainProjection e he hS) = jamesTreeAntichainProjection e he hS := by
  simp only [jamesTreeAntichainProjection, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (jamesTreeFiniteRead e),
    jamesTreeFiniteRead_comp_antichainInsert, ContinuousLinearMap.id_comp]

theorem literalJamesTree_antichain_norm_finite {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hp : p.val ≠ ∞) (a : Fin n → 𝕜) :
    ‖∑ i, a i • jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := literalTreeSegmentFamily) (e i)‖ =
      (∑ i, ‖a i‖ ^ p.val.toReal) ^ (1 / p.val.toReal) :=
  jamesTree_antichain_norm_finite e he literalJamesTreeSegmentsAreChains hp a

theorem consecutiveJamesTree_antichain_norm_finite {n : ℕ} (e : Fin n ↪ DyadicTreeNode)
    (he : IsTreeAntichainEmbedding e) (hp : p.val ≠ ∞) (a : Fin n → 𝕜) :
    ‖∑ i, a i • jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := consecutiveTreeSegmentFamily) (e i)‖ =
      (∑ i, ‖a i‖ ^ p.val.toReal) ^ (1 / p.val.toReal) :=
  jamesTree_antichain_norm_finite e he consecutiveJamesTreeSegmentsAreChains hp a

end ThesisCommon
