import ThesisCommon.Analysis.GowersMaureyIntervalContraction
import ThesisCommon.Analysis.GowersMaureySupportIntervals
import Mathlib.Algebra.BigOperators.Fin

/-! The source's N-interval norms on the actual finite-sequence pre-space.
The supremum is over exactly N successive intervals; empty intervals permit
padding and include the zero-vector cases without additional hypotheses. -/
noncomputable section
open scoped BigOperators NNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

structure FiniteIntervalFamily (N : ℕ) where
  interval : Fin N → Interval
  successive : ∀ i j, i < j → ∀ s ∈ (interval i).set, ∀ t ∈ (interval j).set, s < t

def FiniteIntervalFamily.empty (N : ℕ) : FiniteIntervalFamily N where
  interval _ := Interval.empty
  successive := by simp

instance (N : ℕ) : Nonempty (FiniteIntervalFamily N) := ⟨.empty N⟩

def FiniteIntervalFamily.appendEmpty {N : ℕ} (I : FiniteIntervalFamily N) :
    FiniteIntervalFamily (N + 1) where
  interval := Fin.lastCases Interval.empty I.interval
  successive := by
    intro i j hij s hs t ht
    induction i using Fin.lastCases with
    | last => exact False.elim (not_lt_of_ge (Fin.le_last j) hij)
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp at ht
      | cast j =>
        exact I.successive i j (by simpa using hij) s (by simpa using hs) t (by simpa using ht)

def intervalSum (D : ConstructionData 𝕜) {N : ℕ} (I : FiniteIntervalFamily N) :
    Seminorm 𝕜 (C00 𝕜) := ∑ i, (implicitNorm D).comp (restrict (I.interval i))

theorem intervalSum_apply (D : ConstructionData 𝕜) {N : ℕ}
    (I : FiniteIntervalFamily N) (x : C00 𝕜) :
    intervalSum D I x = ∑ i, implicitNorm D (restrict (I.interval i) x) := by
  simpa [intervalSum] using congrFun (map_sum (Seminorm.coeFnAddMonoidHom 𝕜 (C00 𝕜))
    (fun i => (implicitNorm D).comp (restrict (I.interval i))) Finset.univ) x

theorem intervalSum_le (D : ConstructionData 𝕜) {N : ℕ} (I : FiniteIntervalFamily N) :
    intervalSum D I ≤ (N : ℝ≥0) • implicitNorm D := by
  intro x
  change intervalSum D I x ≤ ((N : ℝ≥0) • implicitNorm D) x
  rw [intervalSum_apply]
  change (∑ i, implicitNorm D (restrict (I.interval i) x)) ≤ (N : ℝ) * implicitNorm D x
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => implicitNorm_restrict_le D (I.interval i) x)

theorem intervalSums_bddAbove (D : ConstructionData 𝕜) (N : ℕ) :
    BddAbove (Set.range (intervalSum D (N := N))) :=
  ⟨(N : ℝ≥0) • implicitNorm D, by rintro _ ⟨I, rfl⟩; exact intervalSum_le D I⟩

def intervalNorm (D : ConstructionData 𝕜) (N : ℕ) : Seminorm 𝕜 (C00 𝕜) :=
  sSup (Set.range (intervalSum D (N := N)))

theorem intervalSum_le_intervalNorm (D : ConstructionData 𝕜) {N : ℕ}
    (I : FiniteIntervalFamily N) : intervalSum D I ≤ intervalNorm D N :=
  le_csSup (intervalSums_bddAbove D N) ⟨I, rfl⟩

theorem intervalNorm_le (D : ConstructionData 𝕜) (N : ℕ) :
    intervalNorm D N ≤ (N : ℝ≥0) • implicitNorm D :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨I, rfl⟩; exact intervalSum_le D I)

theorem intervalSum_appendEmpty (D : ConstructionData 𝕜) {N : ℕ}
    (I : FiniteIntervalFamily N) : intervalSum D I.appendEmpty = intervalSum D I := by
  ext x
  simp [intervalSum_apply, Fin.sum_univ_castSucc, FiniteIntervalFamily.appendEmpty]

theorem intervalNorm_mono (D : ConstructionData 𝕜) : Monotone (intervalNorm D) := by
  apply monotone_nat_of_le_succ
  intro N
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨I, rfl⟩
  rw [← intervalSum_appendEmpty D I]
  exact intervalSum_le_intervalNorm D _

def FiniteIntervalFamily.singleton (E : Interval) : FiniteIntervalFamily 1 where
  interval _ := E
  successive := by intro i j hij; exact False.elim (by omega)

theorem implicitNorm_le_intervalNorm (D : ConstructionData 𝕜) {N : ℕ} (hN : 0 < N) :
    implicitNorm D ≤ intervalNorm D N := by
  intro x
  have h := intervalSum_le_intervalNorm D
    (FiniteIntervalFamily.singleton (supportInterval x)) x
  have h' : implicitNorm D x ≤ intervalNorm D 1 x := by
    simpa [intervalSum_apply, FiniteIntervalFamily.singleton] using h
  exact h'.trans (intervalNorm_mono D hN x)

theorem intervalNorm_one (D : ConstructionData 𝕜) : intervalNorm D 1 = implicitNorm D := by
  apply le_antisymm
  · simpa using intervalNorm_le D 1
  · exact implicitNorm_le_intervalNorm D (by omega)

theorem intervalNorm_restrict_le (D : ConstructionData 𝕜) (N : ℕ)
    (E : Interval) (x : C00 𝕜) : intervalNorm D N (restrict E x) ≤ intervalNorm D N x := by
  rw [intervalNorm, Seminorm.sSup_apply (intervalSums_bddAbove D N)]
  apply ciSup_le
  rintro ⟨_, I, rfl⟩
  change intervalSum D I (restrict E x) ≤ _
  apply le_trans _ (intervalSum_le_intervalNorm D I x)
  change intervalSum D I (restrict E x) ≤ intervalSum D I x
  rw [intervalSum_apply, intervalSum_apply]
  apply Finset.sum_le_sum
  intro i _
  rw [restrict_comm]
  exact implicitNorm_restrict_le D E _

def supportIntervalFamily {N : ℕ} (a : Fin N → C00 𝕜) (ha : Successive a) :
    FiniteIntervalFamily N where
  interval i := supportInterval (a i)
  successive i j hij := supportInterval_successive (ha i j hij)

end ThesisCommon.GowersMaurey
