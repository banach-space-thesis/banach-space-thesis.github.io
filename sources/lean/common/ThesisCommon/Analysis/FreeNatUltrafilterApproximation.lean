import ThesisCommon.Analysis.FreeNatUltrafilterTopology
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyConstant.Basic

/-! Uniform approximation of actual vector-valued continuous functions on
ω* by finite-range locally constant functions. No separability or dimension
restriction on the coefficient space is used in this analytic density step. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

theorem isLocallyConstant_clopen_piecewise {K X : Type*} [TopologicalSpace K]
    {A : Set K} (hA : IsClopen A) {f g : K → X}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (A.piecewise f g) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro U
  by_cases hU : U ∈ A
  · filter_upwards [hA.isOpen.mem_nhds hU, hf.eventually_eq U] with V hV he
    simpa only [Set.piecewise_eq_of_mem, hV, hU] using he
  · filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hU, hg.eventually_eq U] with V hV he
    change V ∉ A at hV
    simpa only [Set.piecewise_eq_of_notMem _ _ _ hV,
      Set.piecewise_eq_of_notMem _ _ _ hU] using he

theorem freeNatUltrafilter_exists_locallyConstant_approximation
    {X : Type*} [NormedAddCommGroup X] (f : C(FreeNatUltrafilter, X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(FreeNatUltrafilter, X), IsLocallyConstant g ∧ ‖f - g‖ ≤ ε := by
  classical
  have hlocal (U : FreeNatUltrafilter) : ∃ A : Set ℕ, A ∈ U ∧
      ∀ V ∈ FreeNatUltrafilter.basic A, ‖f V - f U‖ < ε := by
    obtain ⟨A, hAU, hA⟩ := FreeNatUltrafilter.exists_basic_subset
      ((isOpen_lt (f.continuous.sub continuous_const).norm continuous_const))
      (show U ∈ {V : FreeNatUltrafilter | ‖f V - f U‖ < ε} by simpa using hε)
    exact ⟨A, hAU, hA⟩
  choose A hAU hA using hlocal
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun U => FreeNatUltrafilter.basic (A U))
    (fun U => (FreeNatUltrafilter.isClopen_basic (A U)).isOpen) (by
      intro U _
      exact Set.mem_iUnion.mpr ⟨U, hAU U⟩)
  have hfinite (S : Finset FreeNatUltrafilter) :
      ∃ g : FreeNatUltrafilter → X, IsLocallyConstant g ∧
        ∀ U, (∃ V ∈ S, U ∈ FreeNatUltrafilter.basic (A V)) → ‖f U - g U‖ ≤ ε := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => 0, IsLocallyConstant.const 0, by simp⟩
    | @insert V S hVS ih =>
      obtain ⟨g, hg, hfg⟩ := ih
      let g' := (FreeNatUltrafilter.basic (A V)).piecewise (fun _ => f V) g
      refine ⟨g', isLocallyConstant_clopen_piecewise
        (FreeNatUltrafilter.isClopen_basic (A V)) (IsLocallyConstant.const (f V)) hg, ?_⟩
      intro U hU
      by_cases hUV : U ∈ FreeNatUltrafilter.basic (A V)
      · simpa only [g', Set.piecewise_eq_of_mem _ _ _ hUV] using (hA V U hUV).le
      · obtain ⟨W, hW, hUW⟩ := hU
        have hWS : W ∈ S := by
          rcases Finset.mem_insert.mp hW with rfl | hW
          · exact False.elim (hUV hUW)
          · exact hW
        simpa only [g', Set.piecewise_eq_of_notMem _ _ _ hUV] using
          hfg U ⟨W, hWS, hUW⟩
  obtain ⟨g, hg, hfg⟩ := hfinite S
  refine ⟨⟨g, hg.continuous⟩, hg, (ContinuousMap.norm_le _ hε.le).mpr ?_⟩
  intro U
  apply hfg
  obtain ⟨V, hV⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ U))
  obtain ⟨hVS, hUV⟩ := Set.mem_iUnion.mp hV
  exact ⟨V, hVS, hUV⟩

theorem freeNatUltrafilter_exists_finite_range_approximation
    {X : Type*} [NormedAddCommGroup X] (f : C(FreeNatUltrafilter, X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(FreeNatUltrafilter, X), (Set.range g).Finite ∧ ‖f - g‖ ≤ ε := by
  obtain ⟨g, hg, hfg⟩ := freeNatUltrafilter_exists_locallyConstant_approximation f hε
  exact ⟨g, hg.range_finite, hfg⟩

end ThesisCommon
