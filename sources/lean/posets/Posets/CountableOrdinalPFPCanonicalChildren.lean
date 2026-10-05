import Posets.CountableOrdinalPFPCanonicalCells
import Posets.WolfeDirac

/-! Disjoint canonical child cells at varying ordinal levels. Endpoints and
their entire ceiling fibers lie in successively disjoint ordinal intervals;
the endpoints converge to the prescribed parent point. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinal_exists_canonical_children (θ : Ordinal.{u})
    (A : ℕ → Set Ordinal.{u}) (hA : ∀ n, IsCompact (A n)) (hθ : ∀ n, θ ∈ A n)
    (x : Iic θ) (hc : x.val.card ≤ Cardinal.aleph0)
    (hacc : ∀ n, x.val ∈ derivedSet (A n))
    {H : Set (Iic θ)} (hH : IsClopen H) (hxH : x ∈ H) :
    ∃ y : ℕ → Iic θ,
      (∀ n, y n < x ∧ ∃ hy : (y n).val ∈ A n,
        IsOpen ({⟨(y n).val, hy⟩} : Set (A n))) ∧
      (∀ n, ordinalTowerCell θ (A n) (y n) ⊆ H) ∧
      Pairwise (fun i j => Disjoint (ordinalTowerCell θ (A i) (y i))
        (ordinalTowerCell θ (A j) (y j))) ∧
      Tendsto y atTop (𝓝 x) ∧ closure (⋃ n, ordinalTowerCell θ (A n) (y n)) ⊆ H := by
  classical
  have hxacc : x.val.IsAcc (A 0) := hacc 0
  obtain ⟨r, hr, hcof⟩ := countable_limit_exists_strictMono_cofinal hxacc.isSuccLimit hc
  obtain ⟨b, hbx, hbH⟩ := exists_Ioc_subset_of_mem_nhds
    (hH.isOpen.mem_nhds hxH) ⟨⟨0, Ordinal.zero_le θ⟩, hxacc.pos⟩
  have hex (n : ℕ) (p : Iio x.val) := ordinal_exists_isolated_cell_above θ (hA n) (hθ n)
    (hacc n) (show max p.val (max b.val (r n).val) < x.val from
      max_lt p.property (max_lt hbx (r n).property))
  let chosen (n : ℕ) (p : Iio x.val) : A n := (hex n p).choose
  let step (n : ℕ) (p : Iio x.val) : Iio x.val :=
    ⟨(chosen n p).val, (hex n p).choose_spec.2.1⟩
  have hstep (n : ℕ) (p : Iio x.val) :
      (step n p).val ∈ A n ∧ max p.val (max b.val (r n).val) < (step n p).val ∧
      IsOpen ({⟨(step n p).val, (chosen n p).property⟩} : Set (A n)) ∧
      ∀ z ∈ ordinalTowerCell θ (A n) (step n p).val,
        max p.val (max b.val (r n).val) < z.val ∧ z.val ≤ (step n p).val := by
    exact ⟨(chosen n p).property, (hex n p).choose_spec.1,
      (hex n p).choose_spec.2.2.1, (hex n p).choose_spec.2.2.2⟩
  let z : ℕ → Iio x.val := Nat.rec (step 0 ⟨b.val, hbx⟩) (fun n prev => step (n+1) prev)
  let prev : ℕ → Iio x.val := fun n => match n with
    | 0 => ⟨b.val, hbx⟩
    | n+1 => z n
  have hzstep (n : ℕ) : z n = step n (prev n) := by cases n <;> rfl
  have hzA (n : ℕ) : (z n).val ∈ A n := by rw [hzstep]; exact (hstep n (prev n)).1
  have hzlo (n : ℕ) : max (prev n).val (max b.val (r n).val) < (z n).val := by
    rw [hzstep]; exact (hstep n (prev n)).2.1
  have hziso (n : ℕ) : IsOpen ({⟨(z n).val, hzA n⟩} : Set (A n)) := by
    simpa only [hzstep] using (hstep n (prev n)).2.2.1
  have hzcell (n : ℕ) (w : Iic θ) (hw : w ∈ ordinalTowerCell θ (A n) (z n).val) :
      max (prev n).val (max b.val (r n).val) < w.val ∧ w.val ≤ (z n).val := by
    rw [hzstep] at hw ⊢
    exact (hstep n (prev n)).2.2.2 w hw
  have hzmono : StrictMono (fun n => (z n).val) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (le_max_left _ _).trans_lt (hzlo (n+1))
  let y : ℕ → Iic θ := fun n => ⟨(z n).val, by
    change (z n).val ≤ θ
    exact (show (z n).val < x.val from (z n).property).le.trans x.property⟩
  have hyH (n : ℕ) : ordinalTowerCell θ (A n) (y n) ⊆ H := by
    intro w hw
    obtain ⟨hlo, hhi⟩ := hzcell n w hw
    apply hbH
    change b.val < w.val ∧ w.val ≤ x.val
    exact ⟨(le_max_left b.val (r n).val).trans_lt
      ((le_max_right (prev n).val (max b.val (r n).val)).trans_lt hlo),
      hhi.trans (show (z n).val < x.val from (z n).property).le⟩
  refine ⟨y, ?_, hyH, ?_, ?_, closure_minimal (iUnion_subset hyH) hH.isClosed⟩
  · intro n
    exact ⟨(z n).property, hzA n, hziso n⟩
  · intro i j hij
    suffices hd : ∀ i j : ℕ, i < j → Disjoint (ordinalTowerCell θ (A i) (y i))
        (ordinalTowerCell θ (A j) (y j)) by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hd i j h
      · exact (hd j i h).symm
    intro i j hij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    apply Set.disjoint_left.mpr
    intro w hwi hwj
    have hwi' := (hzcell i w hwi).2
    have hwj' := (le_max_left _ _).trans_lt (hzcell (k+1) w hwj).1
    have hik : i ≤ k := by omega
    exact hwj'.not_ge (hwi'.trans (hzmono.monotone hik))
  · apply tendsto_subtype_rng.mpr
    apply tendsto_order.mpr
    constructor
    · intro a hax
      obtain ⟨N, hN⟩ := hcof a hax
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hN.trans (hr.monotone hn)).trans_lt
        ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt (hzlo n)))
    · intro a hxa
      exact Eventually.of_forall fun n => (z n).property.trans hxa

end Posets
