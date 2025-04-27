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

#check choose_one_right
#check choose_symm_add

set_option linter.unusedTactic false


theorem succ_choose_self (a: ℕ) : choose (a + 1) a = a + 1 := by
  rw [choose_symm_add]
  exact choose_one_right (a + 1)

theorem choose_ge_one {a b : ℕ} (h : a ≥ b) : choose a b ≥ 1 := by
  induction' b with b' ih generalizing a
  · rw [choose_zero_right a]
  · obtain ⟨c, c_eq_succ_a⟩ := exists_eq_add_one.mpr (one_le_of_lt h)
    simp_all [c_eq_succ_a, choose_succ_succ, le_add_right_of_le, ih]

example {a c: ℕ} (h₁ : c ≤ a) : choose a c.succ < choose a.succ c.succ := by
  rw [choose_succ_succ]
  exact Nat.lt_add_of_pos_left (choose_ge_one h₁)

theorem choose_lt_of_lt {a b c: ℕ} (h₁ : c.succ ≤ a) (h₂ : a < b) : choose a c.succ < choose b c.succ := by
  obtain ⟨k, zero_lt_k, a_plus_k_eq_b⟩ := exists_pos_add_of_lt' h₂
  rw [a_plus_k_eq_b.symm]
  have succ_lb := choose_le_choose c.succ (le_of_le_of_eq h₂ a_plus_k_eq_b.symm)
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (choose_ge_one (le_of_succ_le h₁))) succ_lb

theorem succ_le_succ_choose {a b : ℕ} (h : b.succ ≤ a) : a + 1 ≤ choose (a + 1) b.succ := by
  sorry


lemma exists_max_choose_le {m k : ℕ} (one_le_m : 1 ≤ m) (one_le_k : 1 ≤ k):
    ∃ x : ℕ, (x.choose k) ≤ m ∧ ∀ y > x, m < (y.choose k) := by

  by_cases k_ge_m? : k ≥ m
  · use k
    constructor
    · simp [one_le_m]
    · intro y y_gt_k

      by_cases m_eq_k? : m = k
      · simp [m_eq_k?] at *

        -- todo: this case distinction is dumb...
        by_cases y_eq_k_one? : y = k + 1
        · simp [y_eq_k_one?] at *
        · calc k < k + 1               := lt_add_one k
               _ = choose (k + 1) k    := (succ_choose_self k).symm
               _ < choose (k + 2) k    := choose_lt_of_lt (le_add_right k 1) (lt_add_one (k + 1))
               _ <= choose y k         := choose_le_choose k (by
                                            by_contra! y_eq_k_one
                                            push_neg at y_eq_k_one
                                            exact y_eq_k_one? (Nat.eq_of_le_of_lt_succ y_gt_k y_eq_k_one))

      · calc m < k                     := lt_of_le_of_ne k_ge_m? m_eq_k?
             _ < k + 1                 := lt_add_one k
             _ = choose (k + 1) k      := (succ_choose_self k).symm
             _ ≤ choose y k            := choose_le_choose k y_gt_k

  · push_neg at k_ge_m?
    let S := {i | choose i k ≤ m}

    have : S.Finite := by
      have : BddAbove S := by
        use m + 1
        intro s s_in_S
        by_contra! m_one_lt_s

        have := calc m < m + 1              := lt_add_one m
             _ ≤ (m + 1).choose k           := succ_le_succ_choose (one_le_k) (le_of_succ_le k_ge_m?)
             _ < s.choose k                 := choose_lt_choose (le_add_right_of_le (le_of_succ_le k_ge_m?)) m_one_lt_s
             _ ≤ m                          := s_in_S

        exact (lt_self_iff_false m).mp this

      exact Set.finite_iff_bddAbove.mpr this

    have := this.fintype

    have zero_choose_k_le_m := le_of_eq_of_le (choose_eq_zero_iff.mpr one_le_k) (Nat.zero_le m)
    have zero_in_S: 0 ∈ S.toFinset := Set.mem_toFinset.mpr zero_choose_k_le_m
    have S_nonempty : S.toFinset.Nonempty := Set.nonempty_of_mem zero_in_S

    let x := max' S.toFinset S_nonempty
    use x

    constructor

    · have := Set.mem_toFinset.mp (max'_mem S.toFinset S_nonempty)
      exact this -- why???

    · intro y y_gt_x
      have : ¬ choose y k ≤ m := by
        by_contra hc
        have : y ∈ S.toFinset := Set.mem_toFinset.mpr hc
        have : y ≤ x := le_max' S.toFinset y this
        have : y < y := Nat.lt_of_le_of_lt this y_gt_x
        exact (lt_self_iff_false y).mp this

      exact gt_of_not_le this

lemma cascade {m k : ℕ} (one_le_m : 1 ≤ m) (one_le_k : 1 ≤ k) :
    ∃ s, ∃ a : ℕ → ℕ, m = ∑ i ∈ Icc s k, (a i).choose i ∧ 1 ≤ s ∧ s ≤ k := by

  induction' one_le_k with k one_le_k ih generalizing m

  -- Inductive start
  · use 1, (fun _ => m)
    simp [sum_attach]

  -- Inductive step
  · obtain ⟨x, x_choose_k_le_m, x_max⟩ := exists_max_choose_le one_le_m (Nat.le_add_left 1 k)

    by_cases m_eq_x : x.choose (k + 1) = m

    -- Case 1: m = x.choose (k + 1)
    · use k + 1, fun _ => x
      simp [sum_attach, m_eq_x]

    -- Case 2: m < x.choose (k + 1)
    · have x_choose_k_lt_m := lt_of_le_of_ne x_choose_k_le_m m_eq_x
      let m' := m - x.choose (k + 1)
      have one_le_m' : 1 ≤ m':= Nat.le_sub_of_add_le' x_choose_k_lt_m

      obtain ⟨s, a', m'_eq_sum, one_le_s, s_le_k⟩ := ih one_le_m'

      set a := fun i => if i = k + 1 then x else a' i with a_def

      use s, a

      constructor
      · have icc_union : Icc s (k + 1) = (Icc s k) ∪ {k + 1} := by
          ext x
          by_cases x_eq_k_one : x = k+1
          all_goals simp [x_eq_k_one]
          · exact le_add_right_of_le s_le_k
          · exact fun _ => ⟨fun a => le_of_lt_succ (Nat.lt_of_le_of_ne a x_eq_k_one), fun a => le_add_right_of_le a⟩

        have icc_disjoint : Disjoint (Icc s k) {k + 1} := by simp

        have xyz : ∀ i ∈ Icc s k, (a i).choose i = (a' i).choose i := by
          intro i h
          have : i ≠ k + 1:= fun hc => (ne_of_lt (mem_Icc.mp (hc ▸ h)).right) rfl
          simp [this, a_def]

        have foo : m = m' + x.choose (k + 1) := by exact (Nat.sub_eq_iff_eq_add x_choose_k_le_m).mp rfl

        have bar : a (k + 1) = x := by exact if_pos rfl

        simp [icc_union, Finset.sum_union icc_disjoint, foo, bar, m'_eq_sum, sum_congr rfl xyz]

      · exact ⟨one_le_s, le_succ_of_le s_le_k⟩
