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
#check choose_succ_self_right

#check choose_one_right
#check choose_symm_add

set_option linter.unusedTactic false


theorem choose_ge_one_of_ge_one {a b : ℕ} (h : a ≥ 1) : choose a b ≥ 1 := by sorry

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

theorem Icc_succ_eq_union {a b : ℕ} (h : a ≤ b):  Icc a b.succ = Icc a b ∪ { b.succ } := by
  ext x
  by_cases x_eq_b_succ : x = b.succ
  all_goals simp [x_eq_b_succ]
  · simp_all [le_add_right_of_le]
  · intro _; constructor
    all_goals simp_all [le_add_right_of_le, le_of_lt_succ, lt_of_le_of_ne]

lemma cascade {m k : ℕ} (one_le_m : 1 ≤ m) (one_le_k : 1 ≤ k) :
    ∃ s ≤ k, ∃ a : Fin s → ℕ, m = ∑ i, choose (a i) (k - i)
    ∧ (∀ i, k - s ≤ a i) ∧ StrictMono a := by

  -- If 1 ≤ m
  induction' one_le_k with k one_le_k ih generalizing m

  -- Inductive start
  · use 1; simp
    use m; simp_all [StrictMono]

  -- Inductive step
  · set S := {i : Fin m | choose i (k + 1) ≤ m}.toFinset with S_def

    have zero_in_S : ⟨0, one_le_m⟩ ∈ S := by simp [S_def]
    have S_nonempty : S.Nonempty := Set.nonempty_of_mem zero_in_S

    set x := max' S S_nonempty with x_def

    have : choose x (k + 1) ≤ m := by sorry

    set m' := m - choose x (k + 1) with m'_def

    have m_eq_m'_sum := (Nat.sub_eq_iff_eq_add this).mp m'_def.symm

    by_cases m'_eq_zero? : m' = 0

    · use 1; simp
      use fun _ => x
      sorry

    · obtain ⟨s', s'_le_k, a', m'_eq_sum, a'_lb, a'_mono⟩  := ih (one_le_iff_ne_zero.mpr m'_eq_zero? )

      set s := s' + 1 with s_def

      use s; simp [s'_le_k, s_def]

      set a : Fin s → ℕ := by
        intro i; set i' := (i : ℕ) with i'_def
        by_cases i'_eq_zero : i' = 0
        · exact (x : Nat)
        · have i'_pred_lt_one : i' - 1 < s' := Nat.sub_lt_right_of_lt_add (one_le_iff_ne_zero.mpr i'_eq_zero) (i.isLt)
          exact a' ⟨i' - 1, i'_pred_lt_one⟩
        with a_def


      use a

      constructor
      · have one_le_m' : 1 ≤ m' := one_le_iff_ne_zero.mpr m'_eq_zero?

        calc m = choose x (k + 1) + ∑ i , (a' i).choose (k - i)
                    := by simp [m'_eq_sum, Nat.add_comm, m_eq_m'_sum]

             _ = choose x (k + 1) + ∑ i ∈ Ico 0 s', (a' ⟨i, by sorry⟩).choose (k - i)
                    := by sorry

             _ = choose x (k + 1) + ∑ i ∈ Icc 1 s', (a' ⟨i - 1, by sorry⟩).choose (k - (i - 1))
                    := by sorry

             _ = ∑ i ∈ Icc 0 0, choose x (k + 1 - i) + ∑ i ∈ Icc 1 s', (a' ⟨i - 1, by sorry⟩).choose (k + 1 - i)
                    := by sorry

             _ = ∑ i ∈ Icc 0 s', (a i).choose (k + 1 - i)
                    := by sorry

             _ = ∑ i, (a i).choose (k + 1 - i)
                    := by sorry

      · constructor
        · intro i
          by_cases i_eq_zero? : i = 0

          · simp [i_eq_zero?, a_def]
            sorry

          · simp [i_eq_zero?, a_def, s_def, a'_lb, s'_le_k]
            have one_le_i : 1 ≤ (i : ℕ) := one_le_iff_ne_zero.mpr (Fin.val_ne_zero_iff.mpr i_eq_zero?)
            have i_min_1_lt_s : (i : ℕ) - 1 < s' := Nat.sub_lt_right_of_lt_add one_le_i (i.isLt)
            exact le_add_of_sub_le (a'_lb ⟨i - 1, i_min_1_lt_s⟩)


        · intro i j h
          by_cases i_eq_zero? : i = 0
          · sorry

          · have j_ne_zero : j ≠ 0 := by sorry

            simp [a_def, i_eq_zero?, j_ne_zero]

            have : (⟨i -1 , sorry⟩ : Fin s') < (⟨j - 1, sorry⟩ : Fin s') := by sorry

            exact a'_mono this
