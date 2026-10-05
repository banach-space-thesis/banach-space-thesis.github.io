import Sigma.Compacta
import ThesisCommon.Analysis.UnitCharge
import ThesisCommon.Analysis.SeparationCounting

/-! Two-algebra separation and the full counting bound of Lemma 4.3.
Measures here are real finitely additive measures on the disjoint union of
the two countable bases, with total variation at most one. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev PairedMeasure := UnitCharge (ℕ ⊕ ℕ)

def pairedTest (B Btilde : BooleanSubalgebra (Set ℕ)) : B ⊕ Btilde → Set (ℕ ⊕ ℕ)
  | .inl A => Sum.inl '' A.val
  | .inr A => Sum.inr '' A.val

def PairedSeparated (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set PairedMeasure) : Prop :=
  FinitelySeparated (fun μ t => μ (pairedTest B Btilde t)) Set.univ M N

/-- Lemma 4.3. The bound holds also when M is finite; no hypothesis about
cofinality of the continuum, CH, or countable additivity is used. -/
theorem separated_measure_cuts_lt_continuum (B Btilde : BooleanSubalgebra (Set ℕ))
    (hB : #B < 𝔠) (hBtilde : #Btilde < 𝔠) (M : Set PairedMeasure) :
    #{A : Set PairedMeasure // A ⊆ M ∧ PairedSeparated B Btilde A (M \ A)} < 𝔠 := by
  apply separated_cuts_lt_continuum (fun μ t => μ (pairedTest B Btilde t))
    (fun μ t => μ.abs_apply_le_one (pairedTest B Btilde t)) M
  rw [Cardinal.mk_sum]
  simpa only [Cardinal.lift_id] using
    Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hB hBtilde

end SigmaNonprimarity
