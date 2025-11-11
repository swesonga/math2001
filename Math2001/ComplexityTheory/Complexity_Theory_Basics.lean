/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Log
-- TODO: Remove Heather's dependencies
import Library.Basic
import Library.Tactic.ModEq

#eval (0: ℕ) ^ 0

theorem pos_pow_of_0 : ∀ k : ℕ, 0 ^ (k + 1) = 0 := by
  intro k
  calc
    0 ^ (k + 1) = 0 * 0 ^ k := by ring
    _ = 0 := by ring

theorem pos_pow_of_0' : ∀ k : ℕ, (k > 0) → 0 ^ k = 0 := by
  intro k hk
  simple_induction k with k' hk'
  · numbers at hk
  · apply pos_pow_of_0

/-
theorem pow_2_n_ge_pow_n_k : ∀ k : ℕ, forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ k := by
  dsimp
  intro k
  --use (k * Nat.log 2 k)
  use (2 * k ^ 2 + 1)
  intro x h
  simple_induction x with n IH
  /-
  · by_cases h2 : k = 0
    · calc
        2 ^ 0 ≥ 1 := by numbers
        _ = 0 ^ 0 := by ring
        _ = 0 ^ k := by rw [h2]
    · calc
        2 ^ 0 = 1 := by ring
        _ ≥ 0 := by numbers
        _ = 0 ^ k := by ring
  -/
  · by_cases h2 : k ≤ 0
    · -- k ≤ 0
      interval_cases k
      calc
        2 ^ 0 ≥ 1 := by numbers
        _ = 0 ^ 0 := by ring
        --_ = 0 ^ k := by rw [h2]
    · -- ¬ k ≤ 0
      have h3 : k > 0 := by
        apply lt_of_not_le
        apply h2
      calc
        /-
        2 ^ 0 = 1 := by ring
        _ ≥ 0 := by numbers
        _ = 0 * 0 ^ (k - 1) := by ring
        _ = 0 ^ (k - 1 + 1) := by ring
        _ = 0 ^ (k) := by ring
        -/
        0 ^ k = 0 := by apply pos_pow_of_0' k h3
        _ ≤ 1 := by numbers
        _ = 2 ^ 0 := by ring
  · sorry
-/

/-
theorem diff_two : ∀ a b c : ℕ, (a < b) → (b < c) → (c - a) ≥ 2 := by
  intro a b c hab hbc
  simple_induction a with k IH
  · by_cases h : b ≤ 1
    interval_cases b
    · -- b ≤ 1
      by_cases h2 : c ≥ 2
      · -- c ≥ 2
        calc
          c - 0 ≥ 2 - 0 := by rel [h2]
          _ = 2 := by ring
      · -- ¬c ≥ 2
        have h3 : c < 2 := by
          apply lt_of_not_le
          apply h2
        interval_cases c
    · -- ¬b ≤ 1
      have h2 : 1 < b := by
        apply lt_of_not_le
        apply h
      by_cases h3 : b ≤ 2
      · interval_cases b
        calc
          (c : ℤ) - 0 = c := by ring
          _ > 2 := hbc
  · apply pos_pow_of_0
-/

theorem all_nat_ge_0 : ∀n : ℕ, n ≥ 0 := by
  intro n
  simple_induction n with k IH
  · numbers
  · calc
      -- k + 1 ≥ 0 := by numbers
      k + 1 ≥ 0 + 1 := by rel [IH]
      _ = 1 := by ring
      _ ≥ 0 := by numbers

-- Not needed. See pow_n_ge_1_from_c_eq_2 below
theorem pow_2_n_ge_1 : forall_sufficiently_large n : ℕ, 2 ^ n ≥ 1 := by
  dsimp
  use 0
  intro n hn
  simple_induction n with k IH
  · numbers
  · have h1 : 2 ^ k ≥ 1 := by
      apply IH
      apply all_nat_ge_0
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * 1 := by rel [h1]
      _ ≥ 1 := by numbers

theorem pow_c_n_ge_1 : ∀ c n : ℕ, c > 0 → c ^ n ≥ 1 := by
  intro c n hc
  simple_induction n with k IH
  · calc
        c ^ 0 = 1 := by ring
        _ ≥ 1 := by numbers
  · have h1 : 1 ≤ c := by
    -- rw [Nat.lt_succ_iff] at hk
      rw [Nat.succ_le_iff] -- doesn't work with h1 : c ≥ 1
      apply hc
    calc
      c ^ (k + 1) = c * c ^ k := by ring
      _ ≥ 1 * 1 := by rel [IH, h1]

theorem pow_2_n_ge_1' : ∀ n : ℕ, 2 ^ n ≥ 1 := by
  intro n
  apply pow_c_n_ge_1
  numbers

theorem pow_2_n_ge_n : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n := by
  dsimp
  use 0
  intro n hn
  simple_induction n with k IH
  · numbers
  · have h1 : 2 ^ k ≥ k := by
      apply IH
      apply all_nat_ge_0
    by_cases h2 : k ≥ 1
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k := by rel [h1]
      _ = k + k := by ring
      _ ≥ k + 1 := by rel [h2]
    apply lt_of_not_ge at h2
    interval_cases k
    numbers

theorem pow_2_n_ge_n' : ∀ n : ℕ, 2 ^ n ≥ n := by
  intro n
  simple_induction n with k IH
  · numbers
  · by_cases h2 : k ≥ 1
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k := by rel [IH]
      _ = k + k := by ring
      _ ≥ k + 1 := by rel [h2]
    apply lt_of_not_ge at h2
    interval_cases k
    numbers

/-
theorem pow_comp : ∀ m n : ℕ, 2 ^ m ≥ 2 ^ n → m ≥ n := by
  intro m n h
  match m with
  | 0 =>
      -- apply all_nat_ge_0
      --have h1 : 1 ≥ 2 ^n := h
      by_cases ht : n ≤ 0
      · apply ht
      · have h2 : n > 0 := by
          -- apply not_le_of_gt at ht
          apply lt_of_not_le
          apply ht
        by_cases h3 : n ≤ 1
        · interval_cases n
          numbers at h
        · sorry
      calc
        2 ^ n = 2 * 2 ^ (n - 1) := by ring
        _ ≤ 2 * 2 ^ 1 := by ring
  | m' + 1 =>
-/
/-
theorem pow_comp : ∀ m n : ℕ, 2 ^ m ≥ 2 ^ n → m ≥ n := by
  intro m n h
  match n with
  | 0 =>
      apply all_nat_ge_0
  | m' + 1 =>
-/
/-
theorem pow_comp : ∀ m n : ℕ, 2 ^ m ≥ 2 ^ n → m ≥ n := by
  intro m n h
  match m, n with
  | 0, 0 =>
      numbers
  | m' + 1, 0 =>
      apply all_nat_ge_0
  | m', n' + 1 =>
-/

theorem succ_gt_0 : ∀n : ℕ, n + 1 > 0 := by
  intro n
  calc
    n + 1 ≥ 0 + 1 := by extra
    _ > 0 := by numbers

theorem succ_ne_0 : ∀n : ℕ, n + 1 ≠ 0 := by
  intro n
  apply ne_of_gt
  apply succ_gt_0

theorem succ_not_le_0 : ∀n : ℕ, ¬ n + 1 ≤ 0 := by
  intro n hn
  have h1 : n + 1 > 0 := by apply succ_gt_0
  --have h2 : ¬ n + 1 > 0 := by
  apply not_lt_of_le at h1
  · apply h1
  · apply hn

theorem pow_comp : ∀ m n : ℕ, m ≤ n → 2 ^ m ≤ 2 ^ n := by
  intro m n h
  match m, n with
  | 0, 0 =>
      numbers
  | m' + 1, 0 =>
      --apply all_nat_ge_0
      have ht : ¬ m' + 1 ≤ 0 := by
        apply succ_not_le_0
      contradiction
  | m' + 1, n' + 1 =>
      have IHm := pow_comp m' n'
      have hmn : m' ≤ n' := by addarith [h]
      have ht : 2 ^ m' ≤ 2 ^ n' := by
        apply IHm
        apply hmn
      calc
        2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
        _ ≤ 2 * 2 ^ n' := by rel [ht]
        _ = 2 ^ (n' + 1) := by ring
  | 0, n' + 1 =>
      apply pow_2_n_ge_1'

theorem pow_c_n_gt_1 : ∀ c n : ℕ, c > 1 → n > 0 → c ^ n > 1 := by
  intro c n hc hn
  induction_from_starting_point n, hn with k hk IH
  · have h : Nat.succ 0 = 1 := rfl
    rw [h]
    calc
      c ^ 1 = c := by ring
      _ > 1 := hc
  calc
    c ^ (k + 1) = c * c ^ k := by ring
    _ > c * 1 := by rel [IH]
    _ = c := by ring
    _ > 1 := hc

theorem pos_pow_gt_1 : ∀ n : ℕ, n > 0 → 1 < 2 ^ n := by
  intro n hn
  apply pow_c_n_gt_1
  numbers
  apply hn

theorem pow_comp_lt : ∀ m n : ℕ, m < n → 2 ^ m < 2 ^ n := by
  intro m n h
  match m, n with
  | 0, 0 =>
      numbers at h
  | m' + 1, 0 =>
      have ht : ¬ m' + 1 < 0 := by
        apply succ_not_le_0
      contradiction
  | m' + 1, n' + 1 =>
      have IHm := pow_comp_lt m' n'
      have hmn : m' < n' := by addarith [h]
      have ht : 2 ^ m' < 2 ^ n' := by
        apply IHm
        apply hmn
      calc
        2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
        _ < 2 * 2 ^ n' := by rel [ht]
        _ = 2 ^ (n' + 1) := by ring
  | 0, n' + 1 =>
      apply pos_pow_gt_1
      apply h

/-
theorem poly_comp : ∀ c m n : ℕ, (c > 0 ∧ m > 0 ∧ n > 0) → m ≤ n → m ^ c ≤ n ^ c := by
  intro c m n hpos hmn
  obtain ⟨hc, hm, hn⟩ := hpos
  match m, n with
  | 0, 0 =>
      numbers at hm
  | m' + 1, 0 =>
      numbers at hn
  | 0, n' + 1 =>
      numbers at hm
  | m' + 1, n' + 1 =>
      have hmn' : m' ≤ n' := by addarith [hmn]
      calc
        (m' + 1) ^ c = 0 := by ring
        _ ≤ 1 := by numbers
        _ = c ^ 0 := by ring
-/

theorem poly_comp_le : ∀ c m n : ℕ, (c > 0 ∧ m > 0 ∧ n > 0) → m ≤ n → m ^ c ≤ n ^ c := by
  intro c m n hpos hmn
  obtain ⟨hc, hm, hn⟩ := hpos
  match c with
  | 0 =>
      numbers at hc
  | 1 =>
      calc
        m ^ 1 = m := by ring
        _ ≤ n := hmn
        _ = n ^ 1 := by ring
  | c' + 2 =>
      have IH1 := poly_comp_le (c' + 1) m n
      /-
      have ht : m ^ c' ≤ n ^ c' := by
        apply IH1
        constructor
        apply hc
        constructor
        apply hm
        apply hn
        apply hmn
      apply ht
      -/
      have ht : m ^ (c' + 1) ≤ n ^ (c' + 1) := by
        apply IH1
        constructor
        apply succ_gt_0
        constructor
        apply hm
        apply hn
        apply hmn
      calc
        m ^ (c' + 2) = m * m ^ (c' + 1) := by ring
        _ ≤ n * n ^ (c' + 1) := by rel [hmn, ht]
        _ = n ^ (c' + 2) := by ring

theorem poly_comp_lt : ∀ c m n : ℕ, (c > 0 ∧ m > 0 ∧ n > 0) → m < n → m ^ c < n ^ c := by
  intro c m n hpos hmn
  obtain ⟨hc, hm, hn⟩ := hpos
  match c with
  | 0 =>
      numbers at hc
  | 1 =>
      calc
        m ^ 1 = m := by ring
        _ < n := hmn
        _ = n ^ 1 := by ring
  | c' + 2 =>
      have IH1 := poly_comp_lt (c' + 1) m n
      /-
      have ht : m ^ c' ≤ n ^ c' := by
        apply IH1
        constructor
        apply hc
        constructor
        apply hm
        apply hn
        apply hmn
      apply ht
      -/
      have ht : m ^ (c' + 1) < n ^ (c' + 1) := by
        apply IH1
        constructor
        apply succ_gt_0
        constructor
        apply hm
        apply hn
        apply hmn
      calc
        m ^ (c' + 2) = m * m ^ (c' + 1) := by ring
        _ < n * n ^ (c' + 1) := by rel [hmn, ht]
        _ = n ^ (c' + 2) := by ring

theorem pow_le_of_exp_le : ∀ c m n : ℕ, c > 0 → m ≤ n → c ^ m ≤ c ^ n := by
  intro c m n hc h
  match m, n with
  | 0, 0 =>
      calc
        c ^ 0 = 1 := by ring
        _ ≤ 1 := by numbers
        _ = c ^ 0 := by ring
  | m' + 1, 0 =>
      --apply all_nat_ge_0
      have ht : ¬ m' + 1 ≤ 0 := by
        apply succ_not_le_0
      contradiction
  | 0, n' + 1 =>
      apply pow_c_n_ge_1
      apply hc
  | m' + 1, n' + 1 =>
      have IHm := pow_le_of_exp_le c m' n'
      have hmn : m' ≤ n' := by addarith [h]
      have ht : c ^ m' ≤ c ^ n' := by
        apply IHm
        apply hc
        apply hmn
      calc
        c ^ (m' + 1) = c * c ^ m' := by ring
        _ ≤ c * c ^ n' := by rel [ht]
        _ = c ^ (n' + 1) := by ring

theorem pow_n_gt_1_from_c_eq_2 : ∀ c n : ℕ, (c > 1 ∧ n > 0) → c ^ n > 1 := by
  intro c n h
  obtain ⟨hc, hn⟩ := h
  match n with
  | 0 =>
      numbers at hn
  | 1 =>
      calc
        c ^ 1 = c := by ring
        _ > 1 := hc
  | n' + 2 =>
      have IH := pow_n_gt_1_from_c_eq_2 c (n' + 1)
      have ht : c ^ (n' + 1) > 1 := by
        apply IH
        constructor
        apply hc
        apply succ_gt_0
      calc
        c ^ (n' + 2) = c * c ^ (n' + 1) := by ring
        _ > c * 1 := by rel [ht]
        _ = c := by ring
        _ > 1 := hc

theorem pow_n_ge_1_from_c_eq_2 : ∀ c n : ℕ, (c ≥ 1) → c ^ n ≥ 1 := by
  intro c n hc
  match n with
  | 0 =>
      calc
        c ^ 0 = 1 := by ring
        _ ≥ 1 := by numbers
  | n' + 1 =>
      have IH := pow_n_ge_1_from_c_eq_2 c (n')
      have ht : c ^ n' ≥ 1 := by
        apply IH
        apply hc
      calc
        c ^ (n' + 1) = c * c ^ n' := by ring
        _ ≥ c * 1 := by rel [ht]
        _ = c := by ring
        _ ≥ 1 := hc

theorem pow_lt_of_exp_lt : ∀ c m n : ℕ, c > 1 → m < n → c ^ m < c ^ n := by
  intro c m n hc h
  match m, n with
  | 0, 0 =>
      numbers at h
  | m' + 1, 0 =>
      --apply all_nat_ge_0
      have ht : ¬ m' + 1 < 0 := by
        apply succ_not_le_0
      contradiction
  | 0, n' + 1 =>
      --have IHn := pow_lt_of_exp_lt c 0 n'
      apply pow_n_gt_1_from_c_eq_2
      constructor
      apply hc
      apply h
  | m' + 1, n' + 1 =>
      have IHm := pow_lt_of_exp_lt c m' n'
      have hmn : m' < n' := by addarith [h]
      have ht : c ^ m' < c ^ n' := by
        apply IHm
        apply hc
        apply hmn
      calc
        c ^ (m' + 1) = c * c ^ m' := by ring
        _ < c * c ^ n' := by rel [ht]
        _ = c ^ (n' + 1) := by ring

/-
#eval Nat.log 2 1
-- See pow_le_iff_le_log in .lake/packages/mathlib/Mathlib/Data/Nat/Log.lean
theorem discrete_log_comp : ∀ n : ℕ, n > 0 → Nat.log 2 n ≤ n := by
  intro n hn
  match n with
  | 0 =>
      numbers at hn
  | 1 =>
      calc
        Nat.log 2 1 = 0 := by rfl
        _ ≤ 1 := by numbers
  | n' =>
      unfold Nat.log
      dsimp
-/

/-
Nat.log 2 k returns ⌊log_2(k)⌋

TODO: proove this for:
theorem pow_2_n_ge_pow_n_k : ∀ k : ℕ, forall_sufficiently_large n : ℕ, 2 ^ n ≥ (2 ^ (Nat.log 2 n)) ^ k := by
-/
theorem pow_2_n_ge_pow_n_k : ∀ k : ℕ, forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ k := by
  dsimp
  intro k
  /-
  we want g(k) = f(k) / log_2(f(k)) ≥ k
  with f(k) = 2 * k ^ 2, we have log_2(f(k)) = 1 + 2 log_2(k)
  so g(k) = 2 * k ^ 2 / 1 + 2 log_2(k)

  we want g(k) = f(k) / log_2(f(k)) ≥ k
  or g(k) - k ≥ 0
  with f(k) = k ^ 2, we have log_2(f(k)) = 2 log_2(k)
  so g(k) = k ^ 2 / 2 log_2(k) ≥ k for all k ≥ 2
  -/
  match k with
  | 0 =>
      use 0
      intro x hx
      calc
        2 ^ x ≥ 1 := by apply pow_2_n_ge_1'
        _ = x ^ 0 := by ring
  | 1 =>
      use 0
      intro x hx
      calc
        2 ^ x ≥ x := by apply pow_2_n_ge_n'
        -- _ = (2 ^ Nat.log 2 x) := by ring
        _ = x ^ 1 := by ring
  | k' + 2 =>
      use (2 * k' ^ 2)
      intro n hn
      sorry

/-
theorem pow_2_n_ge_pow_n_k2 : ∀ k : ℕ, k ≥ 2 → forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ k := by
  intro k hk
  use (2 * k ^ 2)
  intro n hn
  have ht : n ^ k ≤ 2 ^ n := by
    rw [le_iff_eq_or_lt]
  by_cases h1 : 2 ^ n = n ^ k
  · calc
      2 ^ n = n ^ k := h1
      _ ≥ n ^ k := by extra
  · --apply ge_of_ne
    -- rw [le_iff_eq_or_lt] -- why doesn't this do anything on its own?
    --have ht : 2 ^ n ≥ n ^ k := by
    have ht : n ^ k ≤ 2 ^ n := by
      rw [le_iff_eq_or_lt]

    by_cases h2 : n < Nat.log 2 (n ^ k)
    ·
-/

/-
theorem pow_2_n_ge_pow_n_k3 : ∀ k : ℕ, k ≥ 2 → forall_sufficiently_large n : ℕ, n ^ k ≤ 2 ^ n := by
  intro k hk
  use (2 * k ^ 2)
  intro n hn
  have ht : n ^ k ≤ 2 ^ n := by
    rw [le_iff_eq_or_lt]
    by_cases h1 : 2 ^ n = n ^ k
    · left
      calc
        n ^ k = 2 ^ n := by rw [h1]
    · --apply ge_of_ne
      -- rw [le_iff_eq_or_lt] -- why doesn't this do anything on its own?
      --have ht : 2 ^ n ≥ n ^ k := by
      sorry
  sorry
-/

/-
This is an easier proof to start with
-/
theorem succ_n_lt_pow_2_succ_n : ∀ n : ℕ, n < 2 ^ n := by
  intro n
  simple_induction n with k IH
  · numbers
  · have h : 2 ^ k ≥ 1 := by
      apply pow_n_ge_1_from_c_eq_2
      numbers
    calc
      k + 1 < 2 ^ k + 1 := by rel [IH]
      _ ≤ 2 ^ k + 2 ^ k := by rel [h]
      _ = 2 ^ (k + 1) := by ring

theorem log_2_n_lt_n : ∀ n : ℕ, n ≥ 2 →
  (Nat.log 2 n) < n := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · /-
    Next 2 lines suggested by Copilot with Claude Sonnet 4 agent
    -/
    have h : Nat.log 2 2 = 1 := by rfl
    rw [h]
    numbers
  · /-
    have h_k_gt_0 : k > 0 := calc
      k ≥ 2 := hk
      _ > 0 := by numbers
    have hta : k ≠ 0 := by
      apply ne_of_gt
      apply h_k_gt_0
    have ht1' : 2 ^ (Nat.log 2 k) ≤ k := by
      apply Nat.pow_log_le_self
      apply hta
    have ht1 : 2 ^ (Nat.log 2 k) < 2 ^ k := by
      apply pow_lt_of_exp_lt
      numbers
      apply IH
    have IH' : (Nat.log 2 k) + 1 < k + 1 := by addarith [IH]
    have ht2 : k < 2 ^ ((Nat.log 2 k) + 1) := by
      apply Nat.lt_pow_succ_log_self
      numbers
    /-
    calc
      Nat.log 2 (k + 1) < (Nat.log 2 k) + 1 := by rw [duh]
      --k < 2 ^ ((Nat.log 2 k) + 1) := by rw [Nat.lt_pow_succ_log_self]
      _ < k + 1 := by rel [IH']
    -/
    apply Nat.log_lt_of_lt_pow
    apply succ_ne_0
    have h_k_gt_1 : k > 1 := calc
      k ≥ 2 := hk
      _ > 1 := by numbers
    /-
    calc
      k + 1 < k + k := by rel [h_k_gt_1]
      _ = 2 * k := by ring
      _ < 2 * 2 ^ (Nat.log 2 k + 1) := by rel [ht2]
    -/
    -/
    apply Nat.log_lt_of_lt_pow
    apply succ_ne_0
    apply succ_n_lt_pow_2_succ_n

def is_power_of_2 (n : ℕ) : Prop := n = 2 ^ (Nat.log 2 n)
def is_power_of_2' (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k

theorem succ_even_pow_of_2_lt_pow_succ : ∀ n : ℕ, n > 0 → 2 ^ n + 1 < 2 ^ (n + 1) := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · have ht : 2 ^ k < 2 ^ (k + 1) := by
      apply pow_lt_of_exp_lt
      numbers
      extra
    calc
      2 ^ (k + 1) + 1 = 2 * 2 ^ k + 1 := by ring
      --_ < 2 * 2 ^ k + 1 + 1 := by extra
      _ = 2 ^ k + (2 ^ k + 1) := by ring
      _ < 2 ^ k + 2 ^ (k + 1) := by rel [IH]
      _ < 2 ^ (k + 1) + 2 ^ (k + 1) := by rel [ht]
      _ = 2 * 2 ^ (k + 1) := by ring
      _ = 2 ^ (k + 1 + 1) := by ring

theorem eq_implies_log_eq : ∀ m n : ℕ, m = n → Nat.log 2 m = Nat.log 2 n := by
  intro m n hmn
  calc
    Nat.log 2 m = Nat.log 2 n := by rw [hmn]

theorem log_succ_eq_succ_log : ∀ n : ℕ, n > 1 → is_power_of_2' n → Nat.log 2 (n + 1) = (Nat.log 2 n) := by
  intro n hn h
  obtain ⟨k, h⟩ := h
  have hn_ge_pow_2_k : 2 ^ k ≤ n := calc
    n = 2 ^ k := h
    _ ≥ 2 ^ k := by extra
  --rw [Nat.pow_le_iff_le_log] at hn_ge_pow_2_k
  have ha : 2 ^ k > 0 := calc
    2 ^ k ≥ 1 := by
      apply pow_n_ge_1_from_c_eq_2
      numbers
    _ > 0 := by numbers
  have hb : 2 ^ k ≠ 0 := by
    apply ne_of_gt
    apply ha
  have hc : n < 2 ^ (k + 1) := calc
    n = 2 ^ k := h
    _ = 1 * 2 ^ k := by ring
    --_ < 2 ^ k + 2 ^ k := by extra
    _ < 2 * 2 ^ k := by
      /-
      Copilot prompt: which theorem shows that 1 * x < 2 * x when x > 0?
      -/
      apply mul_lt_mul_of_pos_right
      numbers
      apply ha
    _ = 2 ^ (k + 1) := by ring
  have h0 : Nat.log 2 n = k := by -- TODO: use Nat.log_pow
    rw [Nat.log_eq_iff]
    constructor
    apply hn_ge_pow_2_k
    apply hc
    right
    constructor
    numbers
    apply ne_of_gt
    calc
      0 < 2 ^ k := ha
      _ = n := by rw [h]
  by_cases hk : 0 < k
  · have h1: 2 ^ k + 1 < 2 ^ (k + 1) := by
      apply succ_even_pow_of_2_lt_pow_succ
      apply hk
    --apply Nat.log_lt_of_lt_pow at h1
    have h2 : Nat.log 2 (2 ^ k + 1) < k + 1 := by
      apply Nat.log_lt_of_lt_pow
      apply succ_ne_0
      apply h1
    have h3 : Nat.log 2 (n + 1) < k + 1 := calc
      Nat.log 2 (n + 1) = Nat.log 2 (2 ^ k + 1) := by rw [h]
      _ < k + 1 := h2
    rw [h0]
    rw [Nat.lt_succ_iff] at h3 -- See example 6.2.5
    have h4 : 2 ^ k ≤ 2 ^ k + 1 := by extra
    have h5 : Nat.log 2 (2 ^ k) ≤ Nat.log 2 (2 ^ k + 1) := by
      apply Nat.log_mono_right
      apply h4
    have h5a : Nat.log 2 n = Nat.log 2 (2 ^ k) := by
      apply eq_implies_log_eq
      apply h
    have h5b : Nat.log 2 (n + 1) = Nat.log 2 (2 ^ k + 1) := by
      apply eq_implies_log_eq
      calc
        n + 1 = 2 ^ k + 1 := by rw [h]
        _ = 2 ^ k + 1 := by ring -- why is this necessary?
    have h5c : Nat.log 2 n ≤ Nat.log 2 (n + 1) := calc
      Nat.log 2 n = Nat.log 2 (2 ^ k) := h5a
      _ ≤ Nat.log 2 (2 ^ k + 1) := h5
      _ = Nat.log 2 (n + 1) := by rw [h5b]
    have h6 : k ≤ Nat.log 2 (n + 1) := calc
      k = Nat.log 2 n := by rw [h0]
      _ ≤ Nat.log 2 (n + 1) := h5c
    -- combine h3 and h6
    rw [eq_iff_le_not_lt] -- my first import at top of this file
    constructor
    · apply h3
    · apply Nat.not_lt_of_ge
      apply h6
  · have hk' : k = 0 := by
      apply Nat.eq_zero_of_not_pos
      apply hk
    have hn' : n = 1 := calc
        n = 2 ^ k := h
        _ = 2 ^ 0 := by rw [hk']
        _ = 1 := by ring
    /- We need n > 1
    rw [hn']
    have hl : Nat.log 2 (1 + 1) = 1 := by rfl
    have hr : Nat.log 2 1 = 0 := by rfl
    calc
      Nat.log 2 (1 + 1) = 1 := by rfl
      _ = Nat.log 2 1 := by rfl
    -/
    have hbad : 1 < 1 := calc
      1 < n := hn
      _ = 1 := by rw [hn']
    numbers at hbad

theorem log_pow_add_of_lt {b x y : ℕ} (hb : 1 < b) (hy : y < b ^ x) :
    Nat.log b (b ^ x + y) = x := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · -- Prove b ^ x ≤ b ^ x + y
    -- exact le_add_right (b ^ x) y
    extra
  · -- Prove b ^ x + y < b ^ (x + 1)
    /-
    calc
      b ^ x + y < b ^ x + b ^ x := by rel [hy]
      _ = 2 * b ^ x := by ring
      _ ≤ b * b ^ x := by rel [hb]
      _ = b ^ (x + 1) := by ring
    -/
    -- my proof:
    have h2 : Nat.succ 1 ≤ b := by
      rw [Nat.succ_le]
      apply hb
    calc
      b ^ x + y < b ^ x + b ^ x := by rel [hy]
      _ = 2 * b ^ x := by ring
      _ ≤ b * b ^ x := by rel [h2]
      _ = b ^ (x + 1) := by ring

/-
I want to say that Nat.log 2 (n + 1) = Nat.log 2 n. This holds if n + 1 is not a power of 2.
Otherwise, Nat.log 2 (n + 1) = (Nat.log 2 n) + 1

log_succ_eq_succ_log (above) shows this when n > 1 is a power of two

The proof below should work for any base b > 1. Is it in the standard library?
-/
theorem log_unchanged_adding_smaller_num_to_pow_2_wrong : ∀ m n : ℕ, n > 1 → m < n →
    is_power_of_2' n → Nat.log 2 (2 ^ n + m) = Nat.log 2 (2 ^ n) := by
  intro m n hn hmn h
  calc
    Nat.log 2 (2 ^ n + m) = n := by
      apply log_pow_add_of_lt
      numbers
      calc
        m < n := hmn
        _ < 2 ^ n := by apply succ_n_lt_pow_2_succ_n
    _ = Nat.log 2 (2 ^ n) := by
      rw [Nat.log_pow]
      numbers

-- This is actually what I wanted
theorem log_unchanged_adding_smaller_num_to_pow_2' : ∀ m n : ℕ, n > 1 → m < n →
    is_power_of_2' n → Nat.log 2 (n + m) = Nat.log 2 n := by
  intro m n hn hmn h
  obtain ⟨k, hn⟩ := h
  -- copied ha, hn_ge_pow_2_k, hc and h0 from proof of log_succ_eq_succ_log
  have ha : 2 ^ k > 0 := calc
    2 ^ k ≥ 1 := by
      apply pow_n_ge_1_from_c_eq_2
      numbers
    _ > 0 := by numbers
  have hn_ge_pow_2_k : 2 ^ k ≤ n := calc
    n = 2 ^ k := hn
    _ ≥ 2 ^ k := by extra
  have hc : n < 2 ^ (k + 1) := calc
    n = 2 ^ k := hn
    _ = 1 * 2 ^ k := by ring
    --_ < 2 ^ k + 2 ^ k := by extra
    _ < 2 * 2 ^ k := by
      apply mul_lt_mul_of_pos_right
      numbers
      apply ha
    _ = 2 ^ (k + 1) := by ring
  have h0 : Nat.log 2 n = k := by -- TODO: use Nat.log_pow
    rw [Nat.log_eq_iff]
    constructor
    apply hn_ge_pow_2_k
    apply hc
    right
    constructor
    numbers
    apply ne_of_gt
    calc
      0 < 2 ^ k := ha
      _ = n := by rw [hn]
  rw [h0, hn]
  --have h1 : Nat.log 2 (2 ^ k + m) = Nat.log 2 n := by
  apply log_pow_add_of_lt
  numbers
  calc
    m < n := hmn
    _ = 2 ^ k := by rw [hn]

/-
new idea: why not just obtain the exact power k that's the log of n instead of
complex proofs?
-/
theorem not_pow_of_2_implies_between_consec_pows :
    ∀ n : ℕ, n > 0 → ¬ is_power_of_2' n → ∃ k : ℕ, 2 ^ k < n ∧ n < 2 ^ (k + 1) := by
  intro n hn0 hn
  use Nat.log 2 n
  -- unfold is_power_of_2' at hn
  constructor
  · have h1 : 2 ^ Nat.log 2 n ≤ n := by
      apply Nat.pow_log_le_self
      apply ne_of_gt
      apply hn0
    /-
    apply le_of_eq_or_lt at h1
    apply le_of_lt_or_eq at h1
    -/
    apply lt_or_eq_of_le at h1
    obtain h1l | h1r := h1
    · apply h1l
    · have h_contra : is_power_of_2' n := by
        use Nat.log 2 n
        rw [h1r]
      contradiction
  · calc
      n < 2 ^ (Nat.log 2 n + 1) := by
        apply Nat.lt_pow_succ_log_self
        numbers

theorem not_succ_is_pow_of_2_implies_log_succ_eq_log :
    ∀ n : ℕ, ¬ is_power_of_2' (n + 1) → Nat.log 2 (n + 1) = Nat.log 2 n := by
  intro n h
  -- Note that n ≥ 5, given the hypothesis
  by_cases h0 : n > 1
  · by_cases h1 : is_power_of_2' n
    · -- h1 : is_power_of_2' n
      apply log_unchanged_adding_smaller_num_to_pow_2'
      apply h0
      apply h0
      apply h1
    · -- h1 : ¬is_power_of_2' n
      have htn : ∃ k : ℕ, 2 ^ k < n ∧ n < 2 ^ (k + 1) := by
        apply not_pow_of_2_implies_between_consec_pows
        calc
          n > 1 := h0
          _ > 0 := by numbers
        apply h1
      obtain ⟨k, htnl, htnr⟩ := htn

      /-
      have ht_succ_n : ∃ k : ℕ, 2 ^ k < n + 1 ∧ k < 2 ^ (k + 1) := by
        apply not_pow_of_2_implies_between_consec_pows
        apply succ_gt_0
        apply h
      obtain ⟨k', ht_succ_n_l, ht_succ_n_r⟩ := ht_succ_n
      -/
      have ht1 : 2 ^ k < n + 1 := calc
        2 ^ k < n := htnl
        _ < n + 1 := by extra
      have h_upper : n + 1 < 2 ^ (k + 1) := by
        by_cases h2 : n + 1 = 2 ^ (k + 1)
        · -- h2 : n + 1 = 2 ^ (k + 1)
          have h_contra : is_power_of_2' (n + 1) := by
            use k + 1
            apply h2
          contradiction
        · -- h2 : ¬n + 1 = 2 ^ (k + 1)
          -- whoa, this works even though h2 does not explicitly use the ≠ symbol!
          apply lt_or_gt_of_ne at h2
          obtain h2l | h2r := h2
          · apply h2l
          have h3a : 2 ^ (k + 1) < n + 1 := h2r
          have h3 : 2 ^ (k + 1) ≤ n := by
            rw [Nat.lt_succ_iff] at h3a-- See example 6.2.5
            apply h3a
          have h_contra1 : n < n := calc
            n < 2 ^ (k + 1) := htnr
            _ ≤ n := h3
          have h_contra2 : n = n := by ring
          have h_contra3 : n ≠ n := by
            apply ne_of_lt
            apply h_contra1
          contradiction
      /-
      have ht1 : n < 2 ^ (Nat.log 2 n + 1) := by
        apply Nat.lt_pow_succ_log_self
        numbers
      have ht2 : n + 1 < 2 ^ (Nat.log 2 (n + 1) + 1) := by
        apply Nat.lt_pow_succ_log_self
        numbers
      have h2 : 2 ^ (Nat.log 2 n) < n := by
        apply lt_of_ne
        sorry
      have h3 : 2 ^ (Nat.log 2 n) < n + 1 := by
        calc
          2 ^ (Nat.log 2 n) < n := h2
          _ < n + 1 := by extra
      have h4 : n < 2 ^ (Nat.log 2 n) + 1 := by
        sorry
      have h5 : n + 1 < 2 ^ (Nat.log 2 n) + 1 := by
        sorry
      -/
      have h2 : Nat.log 2 (n + 1) < k + 1 := by
        apply Nat.log_lt_of_lt_pow
        apply succ_ne_0
        apply h_upper
      rw [Nat.lt_succ_iff] at h2 -- See example 6.2.5
      have h3 : Nat.log 2 n < k + 1 := by
        apply Nat.log_lt_of_lt_pow
        apply ne_of_gt
        calc
          n > 1 := h0
          _ > 0 := by numbers
        apply Nat.lt_of_succ_lt
        apply h_upper
      rw [Nat.lt_succ_iff] at h3 -- See example 6.2.5
      have h4 : k ≤ Nat.log 2 n := by
        apply Nat.le_log_of_pow_le
        numbers
        apply le_of_lt
        apply htnl
      have h5: k = Nat.log 2 n := by
        rw [le_antisymm_iff]
        constructor
        apply h4
        apply h3
      /-
      have h_contra : is_power_of_2' n := by
        use k
        calc
          2 ^ k = 2 ^ Nat.log 2 n := by rw [h5]
          _ = n := by
            apply Nat.
      -/
      -- should have tried this earlier
      rw [le_antisymm_iff]
      constructor
      calc
        Nat.log 2 (n + 1) ≤ k := h2
        _ = Nat.log 2 n := h5
      apply Nat.log_mono_right
      extra
  apply le_of_not_gt at h0
  interval_cases n
  rfl
  have h_contra : is_power_of_2' (1 + 1) := by
    use 1
    ring
  contradiction

/-
lemma temp : ∀ n : ℕ, n ≥ 1 → n = n - 1 + 1 := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · ring
  -- interesting how rfl solves this (see Nat.succ_pred)
  calc
    k + (1 : ℤ) - 1 + 1 = (k - 1 + 1) + 1 := by rw [IH]
    --k + 1 = (k - 1 + 1) + 1 := by rw [IH]
-/

lemma my_sub_one_add_one : ∀ n : ℕ, n ≥ 1 → n - 1 + 1 = n := by
  intro n hn
  apply Nat.succ_pred_eq_of_ne_zero
  dsimp
  intro h
  have h_contra : ¬ n = 0 := by
    apply ne_of_gt
    calc
      0 < 1 := by numbers
      _ ≤ n := hn
  contradiction

-- TODO: consider stating this as k < n ∧ ¬ is_power_of_2' n ∧ is_power_of_2' (n + k) → Nat.log 2 (n + k) = Nat.log 2 n + 1
theorem succ_is_pow_of_2_implies_log_succ_eq_succ_log :
    ∀ n : ℕ, n > 0 → is_power_of_2' (n + 1) → Nat.log 2 (n + 1) = Nat.log 2 n + 1 := by
  intro n hn h
  obtain ⟨k, hn2⟩ := h
  -- apply log_succ_eq_succ_log at h
  by_cases h : k ≤ 1
  · interval_cases k
    have h0 : n + 1 = 1 := calc
      n + 1 = 2 ^ 0 := hn2
      _ = 1 := by ring
    have h1 : n = 0 := by
      rw [Nat.add_eq_one_iff] at h0
      obtain h0l | h0r := h0
      · obtain ⟨h1, h2⟩ := h0l
        apply h1
      · obtain ⟨h1, h2⟩ := h0r
        numbers at h2
    have h_contra : ¬ n = 0 := by
      apply ne_of_gt
      apply hn
    contradiction
    have h0 : n + 1 = 2 := calc
      n + 1 = 2 ^ 1 := hn2
      _ = 2 := by ring
    have h1 : n = 1 := by addarith [h0]
    rw [h1]
    have h2a : Nat.log 2 (1 + 1) = 1 := rfl
    have h2b : Nat.log 2 1 + 1 = 1 := rfl
    rw [h2a, h2b]
  have ha : Nat.log 2 n ≤ Nat.log 2 (n + 1) := by
    apply Nat.log_mono_right
    extra
  have hb : k = Nat.log 2 (n + 1) := by
    calc
      k = Nat.log 2 (2 ^ k) := by
        rw [Nat.log_pow]
        numbers
      _ = Nat.log 2 (n + 1) := by rw [hn2]
  have h_k_gt_0 : k > 0 := by
    apply Nat.gt_of_not_le at h
    calc
      k > 1 := h
      _ > 0 := by numbers
  have h_k_ge_2 : k ≥ 2 := by
    --apply Nat.gt_of_not_le at h
    apply Nat.ge_of_not_lt
    intro h'
    interval_cases k
  have ht : k - 1 + 1 = k := by
    apply my_sub_one_add_one
    calc
      k ≥ 2 := h_k_ge_2
      _ ≥ 1 := by numbers
  have hc : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    calc
    /-
      --2 ^ k = 2 * 2 ^ (k - 1) := by ring
      2 ^ (k - 1 + 1) = 2 * 2 ^ (k - 1) := by ring
      _ = 2 ^ (k - 1) + 2 ^ (k - 1) := by ring
    -/
      2 ^ k = 2 ^ (k - 1 + 1) := by rw [ht]
      _ = 2 * 2 ^ (k - 1) := by ring
      _ = 2 ^ (k - 1) + 2 ^ (k - 1) := by ring
  have hd : n = 2 ^ (k - 1) + 2 ^ (k - 1) - 1 := by
    calc
      n = n + 1 - 1 := by
        apply Nat.add_one_sub_one
      _ = 2 ^ k - 1 := by rw [hn2]
      _ = 2 ^ (k - 1) + 2 ^ (k - 1) - 1 := by rw [hc]
  apply Nat.gt_of_not_le at h
  have h_pred_k_gt_0 : k - 1 > 0 := calc
    k - 1 ≥ 2 - 1 := by rel [h_k_ge_2]
    _ > 0 := by numbers
  have he' : 2 ^ (k - 1) > 1 := by
    apply pos_pow_gt_1
    apply h_pred_k_gt_0
  have he : Nat.log 2 (2 ^ (k - 1) + (2 ^ (k - 1) - 1)) = Nat.log 2 (2 ^ (k - 1)) := by
    apply log_unchanged_adding_smaller_num_to_pow_2'
    apply pos_pow_gt_1
    apply h_pred_k_gt_0
    have hf : (2 ^ (k - 1)).pred < 2 ^ (k - 1) := by
      apply Nat.pred_lt
      apply ne_of_gt
      calc
       2 ^ (k - 1) > 1 := he'
       _ > 0 := by numbers
    apply hf
    use k - 1
    ring
  /-
  have he' : 2 ^ (k - 1) + 2 ^ (k - 1) - 1 = 2 ^ (k - 1) + (2 ^ (k - 1) - 1) := by
    apply Nat.add_sub_assoc
  -/
  have h1 : Nat.log 2 n = k - 1 := calc
    Nat.log 2 n = Nat.log 2 (2 ^ (k - 1) + 2 ^ (k - 1) - 1) := by rw [hd]
    _ = Nat.log 2 (2 ^ (k - 1) + (2 ^ (k - 1) - 1)) := by
          rw [Nat.add_sub_assoc]
          apply pow_2_n_ge_1'
    _ = Nat.log 2 (2 ^ (k - 1)) := he
    _ = k - 1 := by
      apply Nat.log_pow
      numbers
  have h2 : k.pred.succ = k := by
    apply Nat.succ_pred
    --apply h
    apply ne_of_gt
    apply h_k_gt_0
  have h3 : k - 1 + 1 = k := by
    apply h2
  calc
    Nat.log 2 (n + 1) = Nat.log 2 (2 ^ k) := by rw [hn2]
    _ = k := by
      apply Nat.log_pow
      numbers
    _ = k - 1 + 1 := by
      rw [h3] -- why doesn't apply h3 work?
    _ = Nat.log 2 n + 1 := by rw [h1]

-- TODO: generalize to a * x + b < 2 ^ x
theorem n_plus_k_lt_2_pow_n : ∀ n : ℕ, n ≥ 3 → 2 * n + 1 < 2 ^ n := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · have ha : 2 ^ 3 ≤ 2 ^ k := by
      apply pow_comp
      apply hk
    have hb : 2 ^ k > 2 := calc
      2 ^ k ≥ 2 ^ 3 := ha
      _ = 8 := by ring
      _ > 2 := by numbers
    calc
      2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
      _ < 2 ^ k + 2 := by rel [IH]
      _ < 2 ^ k + 2 ^ k := by rel [hb]
      _ = 2 ^ (k + 1) := by ring

/-
theorem sq_log_2_n_lt_n_for_n_pow_2 : ∀ n : ℕ, n ≥ 32 → is_power_of_2' n →
  (Nat.log 2 n) ^ 2 < n := by
  intro n hn hn'
  induction_from_starting_point n, hn with k hk IH
  · have h : Nat.log 2 32 = 5 := rfl
    rw [h]
    numbers
-/
theorem sq_log_2_n_lt_n_for_n_pow_2 : ∀ n : ℕ, n ≥ 5 →
  (Nat.log 2 (2 ^ n)) ^ 2 < 2 ^ n := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · have h : Nat.log 2 (2 ^ 5) = 5 := by
      apply Nat.log_pow
      numbers
    rw [h]
    numbers
  have IH' : k ^ 2 < 2 ^ k := calc
    k ^ 2 = Nat.log 2 (2 ^ k) ^ 2 := by
      rw [Nat.log_pow]
      numbers
    _ < 2 ^ k := IH
  have h_2k_gt_1 : 2 * k > 1 := calc
    2 * k ≥ 2 * 5 := by rel [hk]
    _ > 1 := by numbers
  have ha : 2 * k + 1 < 4 * k := calc
    2 * k + 1 < 2 * k + 2 * k := by rel [h_2k_gt_1]
    _ = 4 * k := by ring
  have h' : 2 * k + 1 < 2 ^ k := by
    apply n_plus_k_lt_2_pow_n
    calc
      k ≥ 5 := hk
      _ ≥ 3 := by numbers
  calc
    Nat.log 2 (2 ^ (k + 1)) ^ 2 = (k + 1) ^ 2 := by
      rw [Nat.log_pow]
      numbers
    _ = k ^ 2 + 2 * k + 1 := by ring
    _ < 2 ^ k + 2 * k + 1 := by rel [IH']
    _ = 2 ^ k + (2 * k + 1) := by ring
    _ < 2 ^ k + 2 ^ k := by rel [h']
    _ = 2 ^ (k + 1) := by ring

theorem sq_log_2_n_lt_n : ∀ n : ℕ, n ≥ 31 →
  (Nat.log 2 n) ^ 2 < n := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · /-
    Next 2 lines suggested by Copilot with Claude Sonnet 4 agent
    -/
    have h : Nat.log 2 31 = 4 := by rfl
    rw [h]
    numbers
  · /-
    have h1 : Nat.log 2 k < k := by
      apply log_2_n_lt_n
      calc
        k ≥ 32 := hk
        _ ≥ 2 := by numbers
    -/
    /-
    by_cases h2 : is_power_of_2' k
    · rw [log_succ_eq_succ_log]
      calc
        Nat.log 2 k ^ 2 < k := IH
        _ < k + 1 := by extra
      calc
        k ≥ 32 := hk
        _ > 1 := by numbers
      apply h2
    · -- by_cases h3 : is_power_of_2' (k + 1)
      have h1 : Nat.log 2 k ≤ Nat.log 2 (k + 1) := calc
        Nat.log 2 n = Nat.log 2 (2 ^ k) := h5a
        _ ≤ Nat.log 2 (2 ^ k + 1) := h5
        _ = Nat.log 2 (n + 1) := by rw [h5b]
      have h3 : Nat.log 2 (k + 1) = Nat.log 2 k := by
        -- we need a theorem for this
        sorry
      sorry
    -/
    by_cases h2 : is_power_of_2' (k + 1)
    · -- h2 : is_power_of_2' (k + 1)
      obtain ⟨c, h⟩ := h2
      rw [h]
      apply sq_log_2_n_lt_n_for_n_pow_2
      have ha : 2 ^ c ≥ 2 ^ 5 := calc
        2 ^ c = k + 1 := by rw [h]
        _ ≥ 32 := by addarith [hk]
        _ = 2 ^ 5 := by ring
      by_cases hb : c ≥ 5
      · apply hb
      apply lt_of_not_ge at hb
      interval_cases c <;> numbers at ha
    · -- h2 : ¬is_power_of_2' (k + 1)
      by_cases h3 : is_power_of_2' k
      · rw [log_succ_eq_succ_log]
        calc
          Nat.log 2 k ^ 2 < k := IH
          _ < k + 1 := by extra
        calc
          k ≥ 31 := hk
          _ > 1 := by numbers
        apply h3
      · have h4 : Nat.log 2 (k + 1) = Nat.log 2 k := by
          apply not_succ_is_pow_of_2_implies_log_succ_eq_log
          apply h2
        calc
          Nat.log 2 (k + 1) ^ 2 =  Nat.log 2 k ^ 2 := by rw [h4]
          _ < k := by rel [IH]
          _ < k + 1 := by extra

theorem pow_log_2_n_2_lt_pow_n_2 : ∀ n : ℕ, n ≥ 2 →
  (Nat.log 2 n) ^ 2 < n ^ 2 := by
  intro n hn
  apply poly_comp_lt
  constructor
  numbers
  constructor
  /-
  unfold Nat.log
  dsimp
  have ht : 2 ≤ n ∧ 1 < 2 := by
    constructor
    calc
      2 ≤ 256 := by numbers
      _ ≤ n := hn
    numbers
  rfl
  -/
  apply Nat.log_pos
  numbers
  apply hn
  have h_n_gt_0 : n > 0 := calc -- copied
    n ≥ 2 := hn
    _ > 0 := by numbers
  apply h_n_gt_0
  apply log_2_n_lt_n
  apply hn

theorem pow_log_2_n_2_lt_n : ∀ n : ℕ, n ≥ 256 → Nat.succ (Nat.log 2 n) * Nat.log 2 n < n := by
  intro n hn
  match n with
  | 0 =>
      numbers at hn
  | 1 =>
      numbers at hn
  | n' + 2 =>
      have IH1 := pow_log_2_n_2_lt_n n'
      have IH2 := pow_log_2_n_2_lt_n (n' + 1)
      sorry

theorem pow_2_n_ge_pow_n_k5 : ∀ k n : ℕ, k ≥ 2 ∧ n ≥ 2 ^ k ^ 3 →
  Nat.succ (Nat.log 2 n) * k < n := by
  intro k n hkn
  obtain ⟨hk, hn⟩ := hkn
  -- have h_1_le_2 : 1 ≤ 2 := by numbers
  /-
  have ht0 : k * k ≥ 2 * 2 := by
    calc
      k * k ≥ 2 * k := by rel [hk]
      _ ≥ 2 * 2 := by rel [hk]
  -/
  have ht2 : k * k * k ≥ 2 * 2 * 2 := by
    calc
      k * k * k ≥ 2 * 2 * k := by rel [hk]
      _ ≥ 2 * 2 * 2:= by rel [hk]
  have h_n_lower : n ≥ 256 := by
    calc
      n ≥ 2 ^ (k ^ 3) := hn
      _ = 2 ^ (k * k * k) := by ring
      _ ≥ 2 ^ (2 * 2 * 2) := by --rel [hk]
          apply pow_le_of_exp_le
          numbers
          apply ht2
      _ = 256 := by ring
  have hn' : 2 ^ k ^ 3 ≤ n := hn
  rw [Nat.pow_le_iff_le_log] at hn'
  have ht3 : k ^ 2 < Nat.log 2 n := calc
    k ^ 2 = 1 * k ^ 2 := by ring
    _ < 1 * k ^ 2 + 1 * k ^ 2 := by extra
    _ = 2 * k ^ 2 := by ring
    _ ≤ k * k ^ 2 := by rel [hk]
    _ = k ^ 3 := by ring
    _ ≤ Nat.log 2 n := by rel [hn']
  have ht4 : Nat.succ (Nat.log 2 n) * k = k * Nat.succ (Nat.log 2 n) := by ring
  have h_1_lt_2 : 1 < 2 := by numbers
  have ht5 : Nat.succ (Nat.log 2 n) * k < Nat.succ (Nat.log 2 n) * Nat.log 2 n :=
    calc
      Nat.succ (Nat.log 2 n) * k = Nat.succ (Nat.log 2 n) * k * 1 := by ring
      _ < Nat.succ (Nat.log 2 n) * k * 2 := by rel [h_1_lt_2]
      _ ≤ Nat.succ (Nat.log 2 n) * k * k := by rel [hk]
      _ = Nat.succ (Nat.log 2 n) * k ^ 2 := by ring
      _ < Nat.succ (Nat.log 2 n) * Nat.log 2 n := by rel [ht3]
  have ht5b : Nat.succ (Nat.log 2 n) * Nat.log 2 n = (Nat.log 2 n + 1) * Nat.log 2 n := by
    -- unfold Nat.succ
    rfl -- what the heck? how does this work?
  calc
    Nat.succ (Nat.log 2 n) * k < Nat.succ (Nat.log 2 n) * Nat.log 2 n := ht5
    _ < n := by
      apply pow_log_2_n_2_lt_n
      apply h_n_lower
  numbers
  -- copied from pow_2_n_ge_pow_n_k4
  have h_n_gt_0 : n > 0 := calc
        n ≥ 256 := h_n_lower
        _ > 0 := by numbers
  have ht7: n < 0 ∨ n > 0 := by
    -- apply lt_or_gt_of_ne
    right
    apply h_n_gt_0
  rw [lt_or_lt_iff_ne] at ht7
  apply ht7

-- more succinct proof than log_2_n_lt_n
lemma log_2_n_lt_n' : ∀ n : ℕ,
    n > 0 → Nat.log 2 n < n := by
  intro n hn
  calc
    Nat.log 2 n < n := by
      apply Nat.log_lt_of_lt_pow
      apply ne_of_gt
      apply hn
      apply succ_n_lt_pow_2_succ_n

lemma c_log_n_lt_n : ∀ n c : ℕ,
    n > 0 → forall_sufficiently_large n : ℕ, (Nat.log 2 n) * c < n := by
  intro n k hn
  dsimp
  by_cases h : k < 3
  · interval_cases k
    · use 2
      intro x hx
      calc
        (Nat.log 2 x) * 0 = 0 := by ring
        _ < 2 := by numbers
        _ ≤ x := hx
    · use 2
      intro x hx
      calc
        (Nat.log 2 x) * 1 = Nat.log 2 x := by ring
        _ < x := by
          apply log_2_n_lt_n'
          calc
            x ≥ 2 := hx
            _ > 0 := by numbers
    · use 31 -- instead of 5 since sq_log_2_n_lt_n requires 31
      intro x hx
      have ha : Nat.log 2 31 ≤ Nat.log 2 x := by
        apply Nat.log_monotone
        apply hx
      have hb : Nat.log 2 31 = 4 := rfl
      rw [hb] at ha
      have hc : 2 ≤ Nat.log 2 x := calc
        2 ≤ 4 := by numbers
        _ ≤ Nat.log 2 x := ha
      calc
        (Nat.log 2 x) * 2 ≤ Nat.log 2 x * Nat.log 2 x := by rel [hc]
        _ = (Nat.log 2 x) ^ 2 := by ring
        _ < x := by
          apply sq_log_2_n_lt_n
          apply hx
  use 2 ^ (k ^ 2)
  intro x hx
  have ha : Nat.log 2 (2 ^ k ^ 2) ≤ Nat.log 2 x := by
    apply Nat.log_monotone
    apply hx
    --rw [Nat.pow_le_iff_le_log]
  have hb : Nat.log 2 (2 ^ k ^ 2) = k ^ 2 := by
    apply Nat.log_pow
    numbers
  rw [hb] at ha
  have h_3_le_k : 3 ≤ k := by
    apply Nat.le_of_not_gt
    apply h
  have h_1_le_k : 1 ≤ k := calc
    1 ≤ 3 := by numbers
    _ ≤ k := h_3_le_k
  have hc : k ≤ k ^ 2 := calc
    k = k * 1 := by ring
    _ ≤ k * k := by rel [h_1_le_k]
    _ = k ^ 2 := by ring
  have hd : 2 ^ (k ^ 2) ≥ 2 ^ 9 := by
    apply pow_comp
    calc
      k ^ 2 = k * k := by ring
      _ ≥ 3 * 3 := by rel [h_3_le_k]
  calc
    Nat.log 2 x * k ≤ Nat.log 2 x * k ^ 2 := by rel [hc]
    _ ≤ Nat.log 2 x * Nat.log 2 x := by rel [ha]
    _ = (Nat.log 2 x) ^ 2 := by ring
    _ < x := by
      apply sq_log_2_n_lt_n
      calc
        x ≥ 2 ^ (k ^ 2) := hx
        _ ≥ 2 ^ 9 := hd
        _ ≥ 31 := by numbers

lemma succ_log_2_n_lt_n : ∀ n : ℕ,
    n > 2 → Nat.log 2 n + 1 < n := by
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · have h1 : Nat.succ 2 = 3 := rfl
    have h2 : Nat.log 2 3 = 1 := rfl
    rw [h1, h2]
    calc
      1 + 1 = 2 := by ring
      _ < 3 := by numbers
  by_cases h : is_power_of_2' (k + 1)
  · obtain ⟨k', h'⟩ := h
    have h_k_gt_0 : k > 0 := calc
      k ≥ 3 := hk
      _ > 0 := by numbers
    have h3 : Nat.log 2 (k + 1) = Nat.log 2 k + 1 := by
      apply succ_is_pow_of_2_implies_log_succ_eq_succ_log
      apply h_k_gt_0
      use k'
      apply h'
    rw [h3]
    calc
      Nat.log 2 k + 1 + 1 = (Nat.log 2 k + 1 ) + 1 := by ring
      _ < k + 1 := by rel [IH]
  calc
    Nat.log 2 (k + 1) + 1 = Nat.log 2 k + 1 := by
      rw [not_succ_is_pow_of_2_implies_log_succ_eq_log]
      apply h
    _ < k := IH
  apply Nat.lt_succ_self

lemma c_log_2_n_lt_sq_log_2_n : ∀ c : ℕ,
    forall_sufficiently_large n, c > 0 → (Nat.log 2 n) * c < (Nat.log 2 n) ^ 2 := by
  intro c
  dsimp
  use 2 ^ (c + 1) -- we need c < Nat.log 2 n
  intro n hn hc
  have h1 : 1 ≤ c := by
    rw [Nat.succ_le_iff]
    apply hc
  have h2 : Nat.log 2 (2 ^ (c + 1)) ≤ Nat.log 2 n := by
    apply Nat.log_monotone
    apply hn
  have h3 : Nat.log 2 (2 ^ (c + 1)) = (c + 1) := by
    apply Nat.log_pow
    numbers
  rw [h3] at h2
  apply Nat.lt_of_succ_le at h2
  have h4 : n ≥ 4 := calc
    n ≥ 2 ^ (c + 1) := hn
    _ ≥ 2 ^ (1 + 1) := by
      apply pow_comp
      calc
        1 + 1 ≤ c + 1 := by rel [h1]
        _ = c + 1 := by ring
  have h5 : 0 < Nat.log 2 n := by
    by_cases ht : 0 < Nat.log 2 n
    · apply ht
    apply Nat.le_of_not_lt at ht
    have h_contra : 1 < 0 := calc
      1 ≤ c := h1
      _ < Nat.log 2 n := h2
      _ ≤ 0 := ht
    numbers at h_contra
  calc
    Nat.log 2 n * c < Nat.log 2 n * Nat.log 2 n := by rel [h2]
    _ = Nat.log 2 n ^ 2 := by ring

lemma c_log_2_n_plus_c_lt_sq_log_2_n : ∀ c : ℕ,
    forall_sufficiently_large n, c > 0 → (Nat.log 2 n) * c + c < (Nat.log 2 n) ^ 2 := by
  intro c
  dsimp
  sorry

lemma upper_bound_poly_n_using_power_of_2 : ∀ n k : ℕ,
    n > 0 → k > 0 → n ^ k < (2 ^ (Nat.log 2 n + 1)) ^ k := by
  intro n k hn hk
  have hn' : n < 2 ^ (Nat.log 2 n + 1) := by
    apply Nat.lt_pow_succ_log_self
    numbers
  apply poly_comp_lt
  constructor
  · apply hk
  · constructor
    · apply hn
    calc
      2 ^ (Nat.log 2 n + 1) > n := hn'
      _ > 0 := hn
  apply hn'

/-
Use a power of 2 in the lower bound for n to simplify Nat.log arguments
-/
theorem pow_2_n_ge_pow_n_k4 : ∀ k : ℕ, k ≥ 2 → forall_sufficiently_large n : ℕ, n ^ k < 2 ^ n := by
  intro k hk
  -- use (2 * k ^ 2)
  use 2 ^ (k ^ 2)
  intro n hn
  /-
  have ha : n < 2 ^ (Nat.log 2 n + 1) := by
    apply Nat.lt_pow_succ_log_self
    numbers
  have hb : k - 1 > 0 := calc
    k - 1 ≥ 2 - 1 := by rel [hk]
    _ > 0 := by numbers
  have hb' : n ^ k = n * n ^ (k - 1) := calc
    n ^ k = n * n ^ (k - 1) := by ring
  have hc : n ^ k < 2 ^ ((Nat.log 2 n + 1) * k) := calc
    n ^ k = n * n ^ (k - 1) := hb'
    _ < 2 ^ (Nat.log 2 n + 1) * n ^ (k - 1) := by rel [ha]
    _ = 1 := by ring
  -- why not just show hc as a separate lemma?
  -- done in upper_bound_poly_n_using_power_of_2
  -/
  have h_k_gt_0 : k > 0 := calc
    k ≥ 2 := hk
    _ > 0 := by numbers
  have hn' : n > 0 := calc
    n ≥ 2 ^ (k ^ 2) := hn
    _ ≥ 2 ^ (2 ^ 2) := by
      apply pow_comp
      apply poly_comp_le
      constructor
      · numbers
      · constructor
        · numbers
        apply h_k_gt_0
      apply hk
    _ > 0 := by numbers
  calc
    n ^ k < (2 ^ (Nat.log 2 n + 1)) ^ k := by
      apply upper_bound_poly_n_using_power_of_2
      apply hn'
      apply h_k_gt_0
    _ = 2 ^ ((Nat.log 2 n + 1) * k) := by ring
    _ < 2 ^ n := by
      apply pow_comp_lt
      sorry
  /-_
  rw [le_iff_eq_or_lt]
  by_cases h1 : n ^ k = 2 ^ n
  · left
    apply h1
  · right
    --apply ge_of_ne
    -- rw [le_iff_eq_or_lt] -- why doesn't this do anything on its own?
    have ht1 : 2 ^ (k * k) ≥ 2 ^ (2 * 2) := by
      apply pow_le_of_exp_le
      · numbers
      · calc
          k * k ≥ 2 * k := by rel [hk] -- can't do this in 1 step
          _ ≥ 2 * 2 := by rel [hk]
    have ht2 : n ≥ 16 := by
      calc
      /-
        n ≥ 2 * k ^ 2 := hn
        _ ≥ 2 * 2 ^ 2 := by rel [hk]
      -/
        n ≥ 2 ^ (k ^ 2) := hn
        _ = 2 ^ (k * k) := by ring
        _ ≥ 2 ^ (2 * 2) := ht1
        _ = 16 := by ring
    have h_n_gt_0 : n > 0 := calc
        n ≥ 16 := ht2
        _ > 0 := by numbers
    have ht7: n < 0 ∨ n > 0 := by
      -- apply lt_or_gt_of_ne
      right
      apply h_n_gt_0
    rw [lt_or_lt_iff_ne] at ht7
    /-
    have ht3 : k ^ 2 ≤ Nat.log 2 n := by
      --apply Nat.pow_le_iff_le_log 2 (1 < 2) (n ≠ 0)
      rw [Nat.pow_le_iff_le_log]
      sorry
    -/
    have ht4 : 2 ^ 4 ≤ n := calc
      2 ^ 4 = 16 := by ring
      _ ≤ n := ht2
    rw [Nat.pow_le_iff_le_log] at ht4
    /-
    have ht3 : k ^ 2 ≤ Nat.log 2 n := by
      rw [Nat.pow_le_iff_le_log]
    -/
    have hn' : 2 ^ k ^ 2 ≤ n := hn
    rw [Nat.pow_le_iff_le_log] at hn'
    /-
    I want n ≤ 2 ^ (Nat.log 2 n) + 1
    -/
    have h_n_upper_bound : n < 2 ^ (Nat.log 2 n).succ := by
      apply Nat.lt_pow_succ_log_self
      numbers
    have ht5 : n ^ k < (2 ^ Nat.succ (Nat.log 2 n)) ^ k := by
      apply poly_comp_lt k n (2 ^ Nat.succ (Nat.log 2 n))
      constructor
      calc
        k ≥ 2 := hk
        _ > 0 := by numbers
      constructor
      apply h_n_gt_0
      --apply h_n_upper_bound
      calc
        -- 2 ^ Nat.succ (Nat.log 2 n) = 2 * 2 ^ (Nat.log 2 n) := by ring
        2 ^ Nat.succ (Nat.log 2 n) > n := h_n_upper_bound
        _ > 0 := by extra
      apply h_n_upper_bound
    /-
    have ht8 : Nat.succ (Nat.log 2 n) * k < n := by
      calc
        (Nat.succ (Nat.log 2 n)) * k < (Nat.succ (Nat.log 2 n) * k) * k := by extra
        _ = Nat.succ (Nat.log 2 n) * k ^ 2 := by ring
    -/
    have ht6 : (2 ^ Nat.succ (Nat.log 2 n)) ^ k < 2 ^ n := by
      calc
        (2 ^ Nat.succ (Nat.log 2 n)) ^ k = 2 ^ (Nat.succ (Nat.log 2 n) * k) := by ring
        _ < 2 ^ n := by
          apply pow_lt_of_exp_lt
          numbers
          --apply ht8
          apply pow_2_n_ge_pow_n_k5
          constructor
          apply hk
          sorry
    calc
      n ^ k < (2 ^ Nat.succ (Nat.log 2 n)) ^ k := ht5
      _ < 2 ^ n := ht6
    numbers
    apply ht7
    numbers
    apply ht7
  -/
