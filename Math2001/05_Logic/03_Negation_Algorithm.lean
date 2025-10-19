/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h1 h2
    obtain ⟨hp, hq⟩ := h2
    obtain hnp | hnq := h1
    contradiction
    contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc
    ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    -- ↔ ∃ n : ℤ, ¬ (∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
      ↔ ∃ n : ℤ, ¬ ∃ m : ℤ, (n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ (n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, (¬ n ^ 2 < m ∨ ¬ m < (n + 1) ^ 2) := by rel [not_and_or]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, (n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2) := by rel [not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 ≥ 2 ^ 2 := by rel [hn]
      _ > 2 := by numbers

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    by_cases h2 : P
    · apply h2
    · contradiction
  intro h1 h2
  contradiction

#truth_table ¬(P → Q)

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  /-
  constructor
  intro h1
  constructor
  · by_cases hq : Q
    --
  /-
  · by_cases hp : P
    · apply hp
    · by_cases hq : Q
      · have ht : ¬ P → Q := by
          apply hq
      sorry
  -/
  sorry
  -/
  by_cases hp : P
  · by_cases hq : Q
    · constructor
      · intro h1
        have ht : P → Q := by
          intro hpt
          apply hq
        contradiction
      · intro h1
        obtain ⟨hp2, hnq⟩ := h1
        contradiction
    · constructor
      · intro h
        constructor
        apply hp
        apply hq
      · intro h1 h2
        have : Q := by
          apply h2
          apply hp
        contradiction
  · by_cases hq : Q
    · constructor <;> intro h
      · constructor -- ==>
        · /-
          This morning I reailzed that tried to show ht1 and ht2 and succeeded
          I thought I would need them for ht3 but was obviously wrong. Sometimes
          going to bed is the best way to unblock myself.
          -/
          have ht1: ¬ P → Q := by
            intro h2
            apply hq
          have ht2: P → ¬ Q := by
            intro h2
            contradiction
          have ht3: P → Q := by
            intro h2
            apply hq
          contradiction
        · have : P → Q := by
            intro h
            contradiction
          contradiction
      · -- <==
        obtain ⟨hp2, hq2⟩ := h
        contradiction
    · constructor <;> intro h
      · have : P → Q := by
          intro h
          contradiction
        contradiction
      · obtain ⟨hp2, hq2⟩ := h
        contradiction

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  sorry

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  sorry

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  sorry

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  sorry

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  sorry

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  sorry

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  sorry

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    sorry
  sorry
