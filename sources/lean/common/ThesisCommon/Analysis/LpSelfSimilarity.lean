import ThesisCommon.Analysis.InfinitySelfSimilarity
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Countable flattening for the actual finite-p sum spaces.
Tonelli's theorem for nonnegative real sums identifies the sum of the pth
powers of the inner norms with the sum of all coordinate pth powers.
Together with the infinity construction, this proves self-similarity for
every outer exponent in the papers.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem lp_nested_pair_summable (hp : 0 < p.toReal)
    (x : lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p) :
    Summable (fun ij : ℕ × ℕ => ‖x ij.1 ij.2‖ ^ p.toReal) := by
  apply (summable_prod_of_nonneg (fun ij => Real.rpow_nonneg (norm_nonneg _) _)).mpr
  refine ⟨fun i => (lp.memℓp (x i)).summable hp, ?_⟩
  exact ((lp.memℓp x).summable hp).congr (fun i => lp.norm_rpow_eq_tsum hp (x i))

def lpFiniteFlattenValue (hp : 0 < p.toReal)
    (x : lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p) : lp (fun _ : ℕ => X) p :=
  ⟨fun n => x (Nat.unpair n).1 (Nat.unpair n).2,
    memℓp_gen ((Nat.pairEquiv.symm.summable_iff
      (f := fun ij : ℕ × ℕ => ‖x ij.1 ij.2‖ ^ p.toReal)).mpr
        (lp_nested_pair_summable p hp x))⟩

theorem norm_lpFiniteFlattenValue (hp : 0 < p.toReal)
    (x : lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p) :
    ‖lpFiniteFlattenValue p hp x‖ = ‖x‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  calc
    _ = ∑' n, ‖x (Nat.unpair n).1 (Nat.unpair n).2‖ ^ p.toReal :=
      lp.norm_rpow_eq_tsum hp _
    _ = ∑' ij : ℕ × ℕ, ‖x ij.1 ij.2‖ ^ p.toReal :=
      Nat.pairEquiv.symm.tsum_eq (fun ij : ℕ × ℕ => ‖x ij.1 ij.2‖ ^ p.toReal)
    _ = ∑' i, ∑' j, ‖x i j‖ ^ p.toReal := (lp_nested_pair_summable p hp x).tsum_prod
    _ = ∑' i, ‖x i‖ ^ p.toReal := tsum_congr (fun i => (lp.norm_rpow_eq_tsum hp (x i)).symm)
    _ = ‖x‖ ^ p.toReal := (lp.norm_rpow_eq_tsum hp x).symm

omit [Fact (1 ≤ p)] in
theorem lp_single_pair_summable (hp : 0 < p.toReal) (x : lp (fun _ : ℕ => X) p) :
    Summable (fun ij : ℕ × ℕ => ‖x (Nat.pair ij.1 ij.2)‖ ^ p.toReal) :=
  (Nat.pairEquiv.summable_iff (f := fun n => ‖x n‖ ^ p.toReal)).mpr
    ((lp.memℓp x).summable hp)

def lpFiniteUnflattenValue (hp : 0 < p.toReal) (x : lp (fun _ : ℕ => X) p) :
    lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p :=
  ⟨fun i => lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x, by
    apply memℓp_gen
    have hs := ((summable_prod_of_nonneg (fun ij : ℕ × ℕ =>
      Real.rpow_nonneg (norm_nonneg (x (Nat.pair ij.1 ij.2))) _)).mp
        (lp_single_pair_summable p hp x)).2
    exact hs.congr (fun i => (lp.norm_rpow_eq_tsum hp
      (lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x)).symm)⟩

theorem norm_lpFiniteUnflattenValue (hp : 0 < p.toReal) (x : lp (fun _ : ℕ => X) p) :
    ‖lpFiniteUnflattenValue (𝕜 := 𝕜) p hp x‖ = ‖x‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  calc
    _ = ∑' i, ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x‖ ^ p.toReal :=
      lp.norm_rpow_eq_tsum hp _
    _ = ∑' i, ∑' j, ‖x (Nat.pair i j)‖ ^ p.toReal :=
      tsum_congr (fun i => lp.norm_rpow_eq_tsum hp
        (lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x))
    _ = ∑' ij : ℕ × ℕ, ‖x (Nat.pair ij.1 ij.2)‖ ^ p.toReal :=
      (lp_single_pair_summable p hp x).tsum_prod.symm
    _ = ∑' n, ‖x n‖ ^ p.toReal := Nat.pairEquiv.tsum_eq (fun n => ‖x n‖ ^ p.toReal)
    _ = ‖x‖ ^ p.toReal := (lp.norm_rpow_eq_tsum hp x).symm

def lpFiniteFlatten (hp : 0 < p.toReal) :
    lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p →L[𝕜] lp (fun _ : ℕ => X) p :=
  LinearMap.mkContinuous
    { toFun := lpFiniteFlattenValue p hp
      map_add' := by intros; ext n; rfl
      map_smul' := by intros; ext n; rfl }
    1 (fun x => by
      change ‖lpFiniteFlattenValue p hp x‖ ≤ 1 * ‖x‖
      rw [norm_lpFiniteFlattenValue, one_mul])

def lpFiniteUnflatten (hp : 0 < p.toReal) :
    lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p :=
  LinearMap.mkContinuous
    { toFun := lpFiniteUnflattenValue (𝕜 := 𝕜) p hp
      map_add' := by intros; ext i j; rfl
      map_smul' := by intros; ext i j; rfl }
    1 (fun x => by
      change ‖lpFiniteUnflattenValue (𝕜 := 𝕜) p hp x‖ ≤ 1 * ‖x‖
      rw [norm_lpFiniteUnflattenValue, one_mul])

def lpFiniteFlattenEquiv (hp : 0 < p.toReal) :
    lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p ≃L[𝕜] lp (fun _ : ℕ => X) p :=
  ContinuousLinearEquiv.equivOfInverse (lpFiniteFlatten p hp) (lpFiniteUnflatten p hp)
    (by
      intro x
      ext i j
      change x (Nat.unpair (Nat.pair i j)).1 (Nat.unpair (Nat.pair i j)).2 = x i j
      rw [Nat.unpair_pair])
    (by
      intro x
      ext n
      change x (Nat.pair (Nat.unpair n).1 (Nat.unpair n).2) = x n
      rw [Nat.pair_unpair])

/-- The actual self-similarity equivalence for every p ≥ 1, including ∞. -/
def lpFlattenEquiv :
    lp (fun _ : ℕ => lp (fun _ : ℕ => X) p) p ≃L[𝕜] lp (fun _ : ℕ => X) p := by
  by_cases hp : p = ∞
  · subst p
    exact infinityFlattenEquiv
  · exact lpFiniteFlattenEquiv p (ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp)

theorem lp_sequenceSelfSimilar :
    IsSequenceSelfSimilar 𝕜 (lp (fun _ : ℕ => X) p) :=
  Or.inl ⟨⟨p, Fact.out⟩, ⟨(lpFlattenEquiv p).symm⟩⟩

end ThesisCommon
