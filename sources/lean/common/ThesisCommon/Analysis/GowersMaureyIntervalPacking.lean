import ThesisCommon.Analysis.GowersMaureyIntervalNorms
import Mathlib.Data.Finset.Sort

/-! The disjoint-interval packing estimate behind source Lemma 2. If the
N-interval norm is at most one, the total mass of restrictions whose norm
exceeds 1/N is at most one, for arbitrarily many successive intervals. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def FiniteIntervalFamily.subfamily {M : ℕ} (I : FiniteIntervalFamily M)
    (s : Finset (Fin M)) : FiniteIntervalFamily s.card where
  interval j := I.interval (s.orderEmbOfFin rfl j)
  successive _ _ hij := I.successive _ _ ((s.orderEmbOfFin rfl).strictMono hij)

theorem intervalSum_subfamily (D : ConstructionData 𝕜) {M : ℕ}
    (I : FiniteIntervalFamily M) (s : Finset (Fin M)) (x : C00 𝕜) :
    intervalSum D (I.subfamily s) x = ∑ i ∈ s, implicitNorm D (restrict (I.interval i) x) := by
  rw [intervalSum_apply]
  have h := Finset.sum_map (Finset.univ : Finset (Fin s.card))
    (s.orderEmbOfFin rfl).toEmbedding (fun i => implicitNorm D (restrict (I.interval i) x))
  simpa only [Finset.map_orderEmbOfFin_univ] using h.symm

def FiniteIntervalFamily.take {M N : ℕ} (I : FiniteIntervalFamily M) (h : N ≤ M) :
    FiniteIntervalFamily N where
  interval i := I.interval (Fin.castLE h i)
  successive _ _ hij := I.successive _ _ hij

def largeIntervalWeight (D : ConstructionData 𝕜) (N : ℕ) (x : C00 𝕜) (E : Interval) : ℝ :=
  if (N : ℝ)⁻¹ < implicitNorm D (restrict E x) then implicitNorm D (restrict E x) else 0

theorem largeIntervalWeight_nonneg (D : ConstructionData 𝕜) (N : ℕ) (x : C00 𝕜)
    (E : Interval) : 0 ≤ largeIntervalWeight D N x E := by
  unfold largeIntervalWeight
  split_ifs
  · exact apply_nonneg _ _
  · rfl

theorem largeIntervalWeight_packing (D : ConstructionData 𝕜) {N : ℕ} (hN : 0 < N)
    {x : C00 𝕜} (hx : intervalNorm D N x ≤ 1) {M : ℕ} (I : FiniteIntervalFamily M) :
    (∑ i, largeIntervalWeight D N x (I.interval i)) ≤ 1 := by
  classical
  let s := Finset.univ.filter (fun i => (N : ℝ)⁻¹ < implicitNorm D (restrict (I.interval i) x))
  have hs : s.card ≤ N := by
    by_contra hn
    have hn' : N ≤ s.card := by omega
    let J := (I.subfamily s).take hn'
    have hlt : (N : ℝ)⁻¹ * N < intervalSum D J x := by
      rw [intervalSum_apply]
      have hstrict : (∑ _i : Fin N, (N : ℝ)⁻¹) <
          ∑ i, implicitNorm D (restrict (J.interval i) x) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨⟨0, hN⟩, Finset.mem_univ _⟩
        intro i _
        exact (Finset.mem_filter.mp (s.orderEmbOfFin_mem rfl (Fin.castLE hn' i))).2
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_comm] using hstrict
    have heq : (N : ℝ)⁻¹ * N = 1 := inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hN)
    rw [heq] at hlt
    exact (not_lt_of_ge ((intervalSum_le_intervalNorm D J x).trans hx)) hlt
  calc
    (∑ i, largeIntervalWeight D N x (I.interval i)) =
        ∑ i ∈ s, implicitNorm D (restrict (I.interval i) x) := by
      simp only [s, Finset.sum_filter, largeIntervalWeight]
    _ = intervalSum D (I.subfamily s) x := (intervalSum_subfamily D I s x).symm
    _ ≤ intervalNorm D s.card x := intervalSum_le_intervalNorm D _ x
    _ ≤ intervalNorm D N x := intervalNorm_mono D hs x
    _ ≤ 1 := hx

end ThesisCommon.GowersMaurey
