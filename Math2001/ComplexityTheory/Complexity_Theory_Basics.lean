/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
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

/-
#eval Nat.log 2 1
theorem discrete_log_comp : ∀ n : ℕ, n > 0 → Nat.log 2 n ≤ n := by
  intro n hn
  match n with
  | 1 =>
      calc
        Nat.log 2 1 = 0 := by rfl
        _ ≤ 1 := by numbers
  | n' + 1 =>
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
