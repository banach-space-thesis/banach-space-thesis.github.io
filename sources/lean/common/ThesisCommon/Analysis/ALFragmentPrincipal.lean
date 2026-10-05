import ThesisCommon.Analysis.ALFragmentBasic

/-! Principal fragments in a complete AL-lattice, constructed as actual norm
limits of positive elements of the principal ideal. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
  [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ u v : E, 0 ≤ u → 0 ≤ v → ‖u+v‖ = ‖u‖+‖v‖)
include hAL

theorem al_exists_principal_fragment {a x : E} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    ∃ b : E, IsPositiveFragment b x ∧ a ⊓ x ≤ b ∧
      ∀ z : E, 0 ≤ z → a ⊓ z = 0 → b ⊓ z = 0 := by
  let s := principalPositiveBelow a x
  have hs : s.Nonempty := ⟨0, le_rfl, hx, 0, by simp⟩
  have hpos : ∀ y ∈ s, 0 ≤ y := fun _ hy => hy.1
  have hdir : DirectedOn (· ≤ ·) s := by
    intro u hu v hv
    obtain ⟨hu0,hux,n,hun⟩ := hu
    obtain ⟨hv0,hvx,m,hvm⟩ := hv
    refine ⟨u ⊔ v, ⟨hu0.trans le_sup_left, sup_le hux hvx, n+m, ?_⟩,
      le_sup_left, le_sup_right⟩
    rw [add_nsmul]
    exact sup_le (hun.trans (le_add_of_nonneg_right (nsmul_nonneg ha m)))
      (hvm.trans (le_add_of_nonneg_left (nsmul_nonneg ha n)))
  have hbound : BddAbove (norm '' s) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨y,hy,rfl⟩
    exact norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg hy.1, abs_of_nonneg hx]
      exact hy.2.1)
  obtain ⟨b,hb,u,hu,hlim,_⟩ := al_exists_isLUB_of_directed_norm_bdd hAL hs hpos hdir hbound
  have hb0 : 0 ≤ b := hb.1 ⟨le_rfl,hx,0,by simp⟩
  have hbx : b ≤ x := hb.2 (fun _ hy => hy.2.1)
  have hres : 0 ≤ x-b := sub_nonneg.mpr hbx
  have hzero (z : E) (hz : 0 ≤ z) (hzres : z ≤ x-b)
      (hzprincipal : ∃ n : ℕ, z ≤ n • a) : z = 0 := by
    have hbsub : b ≤ b-z := by
      apply hb.2
      intro y hy
      apply le_sub_iff_add_le.mpr
      apply hb.1
      obtain ⟨n,hn⟩ := hy.2.2
      obtain ⟨m,hm⟩ := hzprincipal
      refine ⟨add_nonneg hy.1 hz, ?_, n+m, ?_⟩
      · calc
          y+z ≤ b+(x-b) := add_le_add (hb.1 hy) hzres
          _ = x := by abel
      · simpa only [add_nsmul] using add_le_add hn hm
    exact le_antisymm (by simpa using (le_sub_iff_add_le.mp hbsub)) hz
  have hares : a ⊓ (x-b) = 0 := hzero _ (le_inf ha hres) inf_le_right ⟨1, by simpa⟩
  have hdisj (z : E) (hz : 0 ≤ z) (haz : a ⊓ z = 0) : b ⊓ z = 0 := by
    have heq (n : ℕ) : u n ⊓ z = 0 := by
      obtain ⟨k,hk⟩ := (hu n).2.2
      exact eq_zero_of_le_nsmul_of_inf_eq_zero ha haz k
        (le_inf (hu n).1 hz) (inf_le_left.trans hk) inf_le_right
    exact tendsto_nhds_unique ((continuous_id.inf continuous_const).tendsto b |>.comp hlim)
      (by
        change Tendsto (fun n => u n ⊓ z) atTop (𝓝 0)
        simp_rw [heq]
        exact tendsto_const_nhds)
  refine ⟨b, ⟨hb0,hbx,hdisj _ hres hares⟩, ?_, hdisj⟩
  exact hb.1 ⟨le_inf ha hx,inf_le_right,1,by simpa using (inf_le_left : a ⊓ x ≤ a)⟩

end ThesisCommon
