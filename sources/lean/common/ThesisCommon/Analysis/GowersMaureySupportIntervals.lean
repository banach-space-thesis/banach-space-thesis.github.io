import ThesisCommon.Analysis.GowersMaureyIntervalGeometry
import ThesisCommon.Analysis.GowersMaureyCoding

/-! Finite support ranges and localisation of the actual coefficient pairing. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def Interval.empty : Interval := ⟨1, 0⟩

@[simp] theorem Interval.set_empty : Interval.empty.set = ∅ := by
  simp [Interval.empty, Interval.set]

@[simp] theorem restrict_empty (x : C00 𝕜) : restrict Interval.empty x = 0 := by
  ext n
  simp

def supportInterval (a : C00 𝕜) : Interval :=
  if h : a.support.Nonempty then ⟨a.support.min' h, a.support.max' h⟩ else Interval.empty

theorem support_subset_supportInterval (a : C00 𝕜) : a.support ⊆ (supportInterval a).set := by
  classical
  intro n hn
  rw [supportInterval, dif_pos ⟨n, hn⟩]
  exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ n hn, Finset.le_max' _ n hn⟩

theorem supportInterval_successive {a b : C00 𝕜} (hab : Before a b) :
    ∀ s ∈ (supportInterval a).set, ∀ t ∈ (supportInterval b).set, s < t := by
  classical
  intro s hs t ht
  by_cases ha : a.support.Nonempty
  · by_cases hb : b.support.Nonempty
    · rw [supportInterval, dif_pos ha] at hs
      rw [supportInterval, dif_pos hb] at ht
      exact (Finset.mem_Icc.mp hs).2.trans_lt
        ((hab _ (Finset.max'_mem _ ha) _ (Finset.min'_mem _ hb)).trans_le
          (Finset.mem_Icc.mp ht).1)
    · simp [supportInterval, hb] at ht
  · simp [supportInterval, ha] at hs

theorem restrict_eq_self_of_support_subset {E : Interval} {x : C00 𝕜}
    (hx : x.support ⊆ E.set) : restrict E x = x := by
  classical
  ext n
  rw [restrict_apply]
  split_ifs with hn
  · rfl
  · exact (Finsupp.notMem_support_iff.mp (fun h => hn (hx h))).symm

@[simp] theorem restrict_supportInterval (x : C00 𝕜) :
    restrict (supportInterval x) x = x :=
  restrict_eq_self_of_support_subset (support_subset_supportInterval x)

theorem pairing_restrict_of_support_subset (a x : C00 𝕜) {E : Interval}
    (ha : a.support ⊆ E.set) : pairing a (restrict E x) = pairing a x := by
  classical
  have h : (pairing a).comp (restrict E) = pairing a := by
    apply Finsupp.lhom_ext
    intro n
    intro c
    change pairing a (restrict E (Finsupp.single n c)) = pairing a (Finsupp.single n c)
    rw [restrict_single]
    split_ifs with hn
    · rfl
    · have hz : a n = 0 := Finsupp.notMem_support_iff.mp (fun h => hn (ha h))
      simp [hz]
  simpa only [LinearMap.sum_apply] using LinearMap.congr_fun h x

@[simp] theorem pairing_restrict_supportInterval (a x : C00 𝕜) :
    pairing a (restrict (supportInterval a) x) = pairing a x :=
  pairing_restrict_of_support_subset a x (support_subset_supportInterval a)

theorem pairing_sum_left {ι : Type*} (s : Finset ι) (a : ι → C00 𝕜) (x : C00 𝕜) :
    pairing (∑ i ∈ s, a i) x = ∑ i ∈ s, pairing (a i) x := by
  classical
  have h : pairing (∑ i ∈ s, a i) = ∑ i ∈ s, pairing (a i) := by
    apply Finsupp.lhom_ext
    intro n
    intro c
    simp [Finset.sum_mul]
  simpa only [LinearMap.sum_apply] using LinearMap.congr_fun h x

theorem pairing_smul_left (c : 𝕜) (a x : C00 𝕜) :
    pairing (c • a) x = c * pairing a x := by
  have h : pairing (c • a) = c • pairing a := by
    apply Finsupp.lhom_ext
    intro n
    intro d
    simp [mul_assoc]
  simpa only [LinearMap.sum_apply] using LinearMap.congr_fun h x

theorem pairing_real_smul_left (r : ℝ) (a x : C00 𝕜) :
    pairing (r • a) x = r • pairing a x := by
  have h : pairing (r • a) = r • pairing a := by
    apply Finsupp.lhom_ext
    intro n
    intro d
    simp
  simpa only [LinearMap.sum_apply] using LinearMap.congr_fun h x

end ThesisCommon.GowersMaurey

