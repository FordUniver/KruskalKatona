import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Finset.Basic

open Nat Finset

#check choose_succ_succ
#check choose_succ_succ'
#check choose_le_add
#check choose_le_choose
#check choose_eq_zero_of_lt


-- can we not explicitly construct x?
lemma exists_max_choose_le {m k : ℕ} (one_le_m : 1 ≤ m) (one_le_k : 1 ≤ k):
    ∃ x : ℕ, (x.choose k) ≤ m ∧ ∀ y > x, m < (y.choose k) := by

  let S := {i ∈ Finset.range m | Nat.choose i k ≤ m}

  have zero_choose_k_le_m := le_of_eq_of_le (choose_eq_zero_iff.mpr one_le_k) (Nat.zero_le m)
  have zero_in_S: 0 ∈ S := Finset.mem_filter.mpr ⟨mem_range.mpr one_le_m, zero_choose_k_le_m⟩

  have S_nonempty : S.Nonempty := Set.nonempty_of_mem zero_in_S

  let x := max' S S_nonempty

  have x_choose_k_le_mn : x.choose k ≤ m := (Finset.mem_filter.mp (max'_mem S S_nonempty)).right

  use x

  constructor
  · exact x_choose_k_le_mn
  · intro y y_gt_x
    have y_not_in_S : y ∉ S := fun hc => (lt_self_iff_false y).mp (lt_of_le_of_lt (le_max' S y hc) y_gt_x)

    by_cases y_le_m : y < m
    · exact gt_of_not_le (fun hc => y_not_in_S (Finset.mem_filter.mpr ⟨mem_range.mpr y_le_m, hc⟩))
    · push_neg at y_le_m
      have : m.choose 1 ≤ m.choose k := by sorry -- monotonicity!
      have : m ≤ m.choose k := le_of_eq_of_le ((choose_one_right m).symm) this
      sorry





lemma cascade {m k : ℕ} (one_le_m : 1 ≤ m) (one_le_k : 1 ≤ k) : ∃ s : ℕ , ∃ a : ℕ → ℕ, 1 ≤ s ∧ s ≤ k ∧
      m = ∑ i ∈ Icc s k, (a i).choose i := by
  induction' k with k ih generalizing m

  -- Induction base
  · contradiction

  -- Induction step
  · obtain ⟨x, x_choose_k_le_m, x_max⟩ := exists_max_choose_le one_le_m one_le_k

    by_cases m_eq_x : x.choose (k + 1) = m

    -- Case 1: m = x.choose (k + 1)
    · use k + 1, fun _ => x
      exact ⟨one_le_k, by rfl, by simp [m_eq_x]⟩

    -- Case 2: m < x.choose (k + 1)
    · have x_choose_k_lt_m := lt_of_le_of_ne x_choose_k_le_m m_eq_x
      let m' := m - x.choose (k + 1)
      have one_le_m' : 1 ≤ m':= Nat.le_sub_of_add_le' x_choose_k_lt_m

      -- instead the induction should just start at 1???
      have k_ge_one : k ≥ 1 := by
        by_contra hc

        have x_one_choose_k_one_le_m : (x + 1).choose (k + 1) ≤ m := by
          simp [Nat.eq_zero_of_not_pos hc] at *
          exact x_choose_k_lt_m

        obtain m_lt_x_one_choose_k_one := x_max (x + 1) (by simp)

        have m_lt_m := lt_of_lt_of_le m_lt_x_one_choose_k_one x_one_choose_k_one_le_m
        exact (lt_self_iff_false m).mp m_lt_m
      -----------

      replace ih := ih one_le_m' k_ge_one

      obtain ⟨s, a, one_le_s, s_le_k, m'_eq_sum⟩ := ih
      use s, fun i => if i = k + 1 then x else a i
      constructor
      · exact one_le_s
      · constructor
        · exact le_add_right_of_le s_le_k
        · have icc_union : Icc s (k + 1) = (Icc s k) ∪ {k + 1} := by
            ext x
            by_cases x_eq_k_one : x = k+1
            all_goals simp [x_eq_k_one]
            · exact le_add_right_of_le s_le_k
            · exact fun _ => ⟨fun a => le_of_lt_succ (Nat.lt_of_le_of_ne a x_eq_k_one), fun a => le_add_right_of_le a⟩

          have icc_disjoint : Disjoint (Icc s k) {k + 1} := by simp

          simp [icc_union, Finset.sum_union icc_disjoint]

          have : ∀ i ∈ Icc s k, (if i = k + 1 then x else a i).choose i = (a i).choose i := by
            intro i h
            have : i ≠ k + 1:= fun hc => (ne_of_lt (mem_Icc.mp (hc ▸ h)).right) rfl
            simp [this]

          simp [sum_congr rfl this, m'_eq_sum.symm]

          exact (Nat.sub_eq_iff_eq_add x_choose_k_le_m).mp rfl
