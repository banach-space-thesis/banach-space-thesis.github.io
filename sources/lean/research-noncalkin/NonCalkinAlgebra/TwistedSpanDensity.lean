import NonCalkinAlgebra.TwistedFiniteSpan
import Mathlib.Topology.Sequences

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
universe u v
variable {G : Type u} [AddCommGroup G]

def innerSpan (c : Cocycle G) : Submodule ℂ (closedSubalgebra c) :=
  Submodule.span ℂ (Set.range (shiftInAlgebra c))

theorem innerSpan_map (c : Cocycle G) :
    (innerSpan c).map (closedSubalgebra c).subtype.toAlgHom.toLinearMap = finiteSpan c := by
  rw [innerSpan, Submodule.map_span, finiteSpan]
  congr 1
  ext a
  constructor
  · rintro ⟨b, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨shiftInAlgebra c g, ⟨g, rfl⟩, rfl⟩

theorem dense_innerSpan (c : Cocycle G) : Dense (innerSpan c : Set (closedSubalgebra c)) := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hx : (x : SquareSummable G →L[ℂ] SquareSummable G) ∈
      closure (finiteSpan c : Set (SquareSummable G →L[ℂ] SquareSummable G)) := by
    rw [← coe_closedSubalgebra_eq_closure]
    exact x.property
  obtain ⟨a, ha, hdist⟩ := Metric.mem_closure_iff.mp hx ε hε
  rw [← innerSpan_map c] at ha
  obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp ha
  refine ⟨b, hb, ?_⟩
  change dist (x : SquareSummable G →L[ℂ] SquareSummable G)
    (b : SquareSummable G →L[ℂ] SquareSummable G) < ε
  change (b : SquareSummable G →L[ℂ] SquareSummable G) = a at hba
  rw [hba]
  exact hdist

/-- Each completed algebra element has a countable set of shifts that
determines its image under every continuous linear map into the algebra. -/
theorem countable_linear_determining_set {A : Type v} [NormedAddCommGroup A]
    [NormedSpace ℂ A] (v : G → A) (hd : Dense (Submodule.span ℂ (Set.range v) : Set A)) (a : A) :
    ∃ S : Set G, S.Countable ∧
      ∀ T U : A →L[ℂ] A, (∀ g ∈ S, T (v g) = U (v g)) → T a = U a := by
  classical
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp (hd a)
  have hrep : ∀ n, ∃ b : G →₀ ℂ, Finsupp.linearCombination ℂ v b = f n := by
    intro n
    have hn := hf n
    rw [← Finsupp.range_linearCombination] at hn
    exact LinearMap.mem_range.mp hn
  choose b hb using hrep
  refine ⟨⋃ n : ℕ, (↑(b n).support : Set G),
    Set.countable_iUnion (fun n => (b n).support.finite_toSet.countable), ?_⟩
  intro T U hTU
  have hclosed : IsClosed {x : A | T x = U x} :=
    isClosed_eq T.continuous U.continuous
  apply hclosed.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  change T (f n) = U (f n)
  rw [← hb n, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g hg
  rw [hTU g (Set.mem_iUnion.mpr ⟨n, hg⟩)]

theorem countable_shift_determining_set (c : Cocycle G) (a : closedSubalgebra c) :
    ∃ S : Set G, S.Countable ∧
      ∀ T U : closedSubalgebra c →L[ℂ] closedSubalgebra c,
        (∀ g ∈ S, T (shiftInAlgebra c g) = U (shiftInAlgebra c g)) → T a = U a :=
  countable_linear_determining_set (shiftInAlgebra c) (dense_innerSpan c) a

end NonCalkinAlgebra.TwistedRegular
