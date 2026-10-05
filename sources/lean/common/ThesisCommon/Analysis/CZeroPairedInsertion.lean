import ThesisCommon.Analysis.CZeroOperators

/-! Contractive insertion into consecutive pairs of a selected c₀ sequence. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def cZeroPairValue (x : CZeroSum 𝕜) : CZeroSum 𝕜 where
  toFun n := if n % 2 = 0 then x (n / 2) else -x (n / 2)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
      tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨2*b, by intro n hn; omega⟩)
    have hx : Tendsto (fun n => ‖x (n / 2)‖) atTop (𝓝 0) := by
      have h := x.zero_at_infty'.norm
      rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop, norm_zero] at h
      exact h.comp hdiv
    exact squeeze_zero_norm (fun n => by split_ifs <;> simp) hx

theorem norm_cZeroPairValue_le (x : CZeroSum 𝕜) : ‖cZeroPairValue x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).2
  intro n
  change ‖if n % 2 = 0 then x (n / 2) else -x (n / 2)‖ ≤ ‖x‖
  split_ifs <;> simpa only [norm_neg] using
    BoundedContinuousFunction.norm_coe_le_norm x.toBCF (n / 2)

def cZeroPairMap : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜 :=
  LinearMap.mkContinuous
    { toFun := cZeroPairValue
      map_add' := by intro x y; ext n; change (if _ then _ else _) = _;
                     split_ifs <;> simp_all [cZeroPairValue, add_comm]
      map_smul' := by intro a x; ext n; change (if _ then _ else _) = _;
                      split_ifs <;> simp_all [cZeroPairValue] }
    1 (fun x => by simpa using norm_cZeroPairValue_le x)

theorem norm_cZeroPairMap_le : ‖cZeroPairMap (𝕜 := 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def cZeroPairedInsertion (s : ℕ → ℕ) (hs : StrictMono s) :
    CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜 :=
  (cZeroExtend (𝕜 := 𝕜) ⟨s, hs.injective⟩).comp cZeroPairMap

theorem norm_cZeroPairedInsertion_le (s : ℕ → ℕ) (hs : StrictMono s) :
    ‖cZeroPairedInsertion (𝕜 := 𝕜) s hs‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_cZeroExtend_le ⟨s, hs.injective⟩) norm_cZeroPairMap_le
      (norm_nonneg (cZeroPairMap (𝕜 := 𝕜))) zero_le_one).trans_eq (one_mul 1))

@[simp] theorem cZeroPairedInsertion_even (s : ℕ → ℕ) (hs : StrictMono s)
    (x : CZeroSum 𝕜) (n : ℕ) : cZeroPairedInsertion s hs x (s (2*n)) = x n := by
  change cZeroExtend (𝕜 := 𝕜) ⟨s, hs.injective⟩ (cZeroPairMap x) (s (2*n)) = _
  trans cZeroPairMap x (2*n)
  · exact cZeroExtend_apply_image (𝕜 := 𝕜) ⟨s, hs.injective⟩ (cZeroPairMap x) (2*n)
  change (if (2*n) % 2 = 0 then x ((2*n) / 2) else -x ((2*n) / 2)) = _
  simp

@[simp] theorem cZeroPairedInsertion_odd (s : ℕ → ℕ) (hs : StrictMono s)
    (x : CZeroSum 𝕜) (n : ℕ) : cZeroPairedInsertion s hs x (s (2*n+1)) = -x n := by
  change cZeroExtend (𝕜 := 𝕜) ⟨s, hs.injective⟩ (cZeroPairMap x) (s (2*n+1)) = _
  trans cZeroPairMap x (2*n+1)
  · exact cZeroExtend_apply_image (𝕜 := 𝕜) ⟨s, hs.injective⟩ (cZeroPairMap x) (2*n+1)
  change (if (2*n+1) % 2 = 0 then x ((2*n+1) / 2) else -x ((2*n+1) / 2)) = _
  simp [Nat.add_div]

end ThesisCommon

