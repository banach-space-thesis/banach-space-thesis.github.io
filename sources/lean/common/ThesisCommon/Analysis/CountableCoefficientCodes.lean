import ThesisCommon.Analysis.ContinuumScheduling
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! The cardinality and bounded support of countably supported coefficient
codes. These estimates apply to actual ell-one vectors. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon

def CountableCoefficientCode (ι : Type) := {f : ι → ℝ // (Function.support f).Countable}

theorem countableCoefficientCode_cardinal_le {ι : Type} [Nonempty ι] (hι : #ι ≤ 𝔠) :
    #(CountableCoefficientCode ι) ≤ 𝔠 := by
  classical
  have henum (f : CountableCoefficientCode ι) : ∃ e : ℕ → ι, Function.support f.val ⊆ Set.range e :=
    Set.countable_iff_exists_subset_range.mp f.property
  choose e he using henum
  let encode : CountableCoefficientCode ι → (ℕ → ι × ℝ) := fun f n => (e f n, f.val (e f n))
  have hinj : Function.Injective encode := by
    intro f g h
    have heq (n : ℕ) : e f n = e g n := congrArg Prod.fst (congrFun h n)
    have hval (n : ℕ) : f.val (e f n) = g.val (e g n) := congrArg Prod.snd (congrFun h n)
    apply Subtype.ext
    funext i
    by_cases hf : f.val i = 0
    · by_cases hg : g.val i = 0
      · exact hf.trans hg.symm
      · obtain ⟨n,hn⟩ := he g hg
        have hv := hval n
        rwa [heq n, hn] at hv
    · obtain ⟨n,hn⟩ := he f hf
      have hv := hval n
      rwa [← heq n, hn] at hv
  apply (Cardinal.mk_le_of_injective hinj).trans
  rw [Cardinal.mk_arrow, Cardinal.mk_prod, Cardinal.mk_real, Cardinal.mk_nat]
  simp only [Cardinal.lift_id]
  apply (Cardinal.power_le_power_right (mul_le_mul_right' hι 𝔠)).trans
  rw [Cardinal.continuum_mul_self, Cardinal.continuum_power_aleph0]

theorem lp_one_countable_support {ι : Type*} (f : lp (fun _ : ι => ℝ) 1) :
    (Function.support f).Countable := by
  have hs : Summable (fun i => ‖f i‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) f).summable
  simpa only [Function.support, norm_ne_zero_iff] using hs.countable_support

theorem lp_one_cardinal_le_continuum {ι : Type} [Nonempty ι] (hι : #ι ≤ 𝔠) :
    #(lp (fun _ : ι => ℝ) 1) ≤ 𝔠 := by
  let f : lp (fun _ : ι => ℝ) 1 → CountableCoefficientCode ι :=
    fun x => ⟨x,lp_one_countable_support x⟩
  have hf : Function.Injective f := by
    intro x y h
    apply lp.ext
    exact congrArg (fun z : CountableCoefficientCode ι => z.val) h
  exact (Cardinal.mk_le_of_injective hf).trans (countableCoefficientCode_cardinal_le hι)

theorem lp_one_sequence_support_bounded
    (f : ℕ → lp (fun _ : (𝔠 : Cardinal.{0}).ord.toType => ℝ) 1) :
    ∃ a, ∀ n b, f n b ≠ 0 → b < a := by
  have hc : (⋃ n, Function.support (f n)).Countable :=
    Set.countable_iUnion (fun n => lp_one_countable_support (f n))
  obtain ⟨a,ha⟩ := countable_below_continuum_stage hc
  exact ⟨a,fun n b hb => ha b (Set.mem_iUnion.mpr ⟨n,hb⟩)⟩

end ThesisCommon
