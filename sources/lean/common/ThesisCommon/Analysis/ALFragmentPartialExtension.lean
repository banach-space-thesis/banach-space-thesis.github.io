import ThesisCommon.Analysis.BooleanPartialIsometryOfIso
import ThesisCommon.Analysis.BooleanPartialIsometryClosure
import ThesisCommon.Analysis.BooleanPartialIsometryCardinality
import ThesisCommon.Analysis.ALFragmentStrictContent
import ThesisCommon.Analysis.ALFragmentIsometryContent
import ThesisCommon.Analysis.ALFragmentClosureDensity

/-! Matching intersection masses in the completed small algebras gives an
actual one-generator extension of the original partial metric isomorphism. -/
noncomputable section
open Set Cardinal
open scoped symmDiff
namespace ThesisCommon
universe u
variable {E F : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [HasSolidNorm F] [CompleteSpace F]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)] (f : F) [Fact (0 ≤ f)]

theorem preserves_alFragmentStrictContent_of_isometry
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f)) (φ : S ≃o T) (hφ : Isometry φ)
    (a : S) : alFragmentStrictContent hF f (φ a).val = alFragmentStrictContent hE e a.val := by
  exact norm_positiveFragmentValue_eq_of_isometry e f S T φ hφ a

theorem exists_alFragment_partialIsometry_extension_of_matching
    (κ : Cardinal.{u})
    (matching : ∀ (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
      (T : BooleanSubalgebra (PositiveFragmentAlgebra f)),
      IsClosed (S : Set (PositiveFragmentAlgebra e)) →
      IsClosed (T : Set (PositiveFragmentAlgebra f)) → topologicalDensity T < κ →
      ∀ φ : S ≃o T,
      (∀ s : S, alFragmentStrictContent hF f (φ s).val = alFragmentStrictContent hE e s.val) →
      ∀ a : PositiveFragmentAlgebra e, ∃ b : PositiveFragmentAlgebra f,
      ∀ s : S, alFragmentStrictContent hF f ((φ s).val ⊓ b) =
        alFragmentStrictContent hE e (s.val ⊓ a))
    (p : BooleanPartialIsometry (PositiveFragmentAlgebra e) (PositiveFragmentAlgebra f))
    (hp : #p.source < κ) (a : PositiveFragmentAlgebra e) :
    ∃ q : BooleanPartialIsometry (PositiveFragmentAlgebra e) (PositiveFragmentAlgebra f),
      p ≤ q ∧ a ∈ q.source ∧ #q.source ≤ #p.source * #p.source := by
  let c := p.metricClosure (continuous_positiveFragment_compl e) (continuous_positiveFragment_compl f)
  have hpc : p ≤ c := p.le_metricClosure _ _
  have hcsmall : topologicalDensity c.target < κ := by
    apply (p.density_metricClosure_target_le _ _).trans_lt
    rwa [BooleanPartialIsometry.cardinal_target_eq_source]
  have hccont := preserves_alFragmentStrictContent_of_isometry hE hF e f
    c.source c.target c.orderIso c.orderIso_isometry
  obtain ⟨b, hb⟩ := matching c.source c.target
    (p.isClosed_metricClosure_source _ _) (p.isClosed_metricClosure_target _ _)
    hcsmall c.orderIso hccont a
  have hpcont := preserves_alFragmentStrictContent_of_isometry hE hF e f
    p.source p.target p.orderIso p.orderIso_isometry
  have hab (s : p.source) :
      alFragmentStrictContent hF f ((p.orderIso s).val ⊓ b) =
        alFragmentStrictContent hE e (s.val ⊓ a) := by
    have h := hb ⟨s.val, BooleanPartialIsometry.source_mono hpc s.property⟩
    rwa [BooleanPartialIsometry.orderIso_extension hpc s] at h
  obtain ⟨g, hgext, hga, hgcontent⟩ := exists_booleanOrderIso_adjoin_generator
    (alFragmentStrictContent hE e) (alFragmentStrictContent hF f)
    p.source p.target p.orderIso hpcont a b hab
  have hgiso := isometry_of_preserves_alFragmentStrictContent hE e hF f
    (booleanAdjoinOne p.source a) (booleanAdjoinOne p.target b) g hgcontent
  let q := BooleanPartialIsometry.ofOrderIso _ _ g hgiso
  refine ⟨q, ?_, ?_, ?_⟩
  · exact BooleanPartialIsometry.le_ofOrderIso_of_extends p _ _ g hgiso
      (fun x hx => booleanAdjoinOne_base p.source a hx) hgext
  · change a ∈ (BooleanPartialIsometry.ofOrderIso _ _ g hgiso).source
    rw [BooleanPartialIsometry.ofOrderIso_source]
    exact booleanAdjoinOne_generator p.source a
  · change #(BooleanPartialIsometry.ofOrderIso _ _ g hgiso).source ≤ _
    rw [BooleanPartialIsometry.ofOrderIso_source]
    simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
      Cardinal.mk_le_of_surjective (booleanAdjoinOnePairMap_surjective p.source a)

end ThesisCommon
