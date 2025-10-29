/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x2, hx2⟩ := IH
    · right
      use x
      calc
        k + 1 = 2 * x + 1 := by rw [hx]
        _ = 2 * x + 1 := by ring -- TODO: why does it fail without this line?
    · left
      use x2 + 1
      calc
        k + 1 = 2 * x2 + 1 + 1 := by rw [hx2]
        _ = 2 * (x2 + 1) := by ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · use 0
    /-
    dsimp [Int.ModEq] at *
    dsimp [(· ∣ · )] at h
    -/
    --obtain c | hc = h  -- these failed because I needed := instead of =
    --obtain ⟨c, hc⟩ = h
    calc
      a ^ 0 - b ^ 0 = 1 - 1 := by ring
      _ = 0 := by ring
      _ = d * 0 := by ring
  · dsimp [Int.ModEq] at *
    dsimp [(· ∣ · )] at *
    obtain ⟨x, h1⟩ := IH
    obtain ⟨y, h2⟩ := h
    have ht := calc
      a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
      _ = a * (d * x) + b ^ k * (d * y) := by rw [h1, h2]
      _ = d * (a * x) + d * (b ^ k * y) := by ring
      _ = d * (a * x + b ^ k * y) := by ring
    use a * x + b ^ k * y
    apply ht

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    have ht : 2 * 4 ≥ 1 := by numbers
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k  * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ ≥ k ^ 2 + 2 * k + 1 := by rel [ht]
      _ = (k + 1) ^ 2 := by ring


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  · numbers
  · -- have ht : k - k = 0 := by numbers
    /-
    calc
      3 ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (k ^ 2 + k + 1) := by rel [IH]
      -- _ = 3 * (k ^ 2 + k + 1 + k - k) := by ring
      -- _ = 3 * ((k + 1) ^ 2 - k) := by ring
      /-
      _ = 3 * k ^ 2 + 3 * k + 3 := by ring
      _ = 3 * k ^ 2 + 3 * k + 3 + 6 * k - 3 * k := by ring
      -/
    -/
    /-
    Working in the opposite direction made this problem trivial
    -/
    calc
      (k + 1) ^ 2 + (k + 1) + 1 = k ^ 2 + 3 * k + 3 := by ring
      _ ≤ k ^ 2 + 3 * k + 3 + 2 * k ^ 2 := by extra
      _ = 3 * (k ^ 2 + k + 1) := by ring
      _ ≤ 3 * (3 ^ k) := by rel [IH]
      _ = 3 ^ (k + 1) := by ring

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · calc
      (1 + a) ^ 0 = 1 := by ring
      _ ≥ 1 + 0 := by numbers
      _ = 1 + 0 * a := by ring
  · by_cases h: a ≥ 0
    calc
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [IH]
      _ = 1 + k * a + a * (1 + k * a) := by ring
      _ = 1 + (k + 1) * a + a ^ 2 * k := by ring
      _ ≥ 1 + (k + 1) * a := by extra
    have h_a_lt_0 : a < 0 := lt_of_not_ge h
    /-
    Pasting the above calc block gives this error on the by rel [IH]:

    rel failed, cannot prove goal by 'substituting' the listed relationships.
    The steps which could not be automatically justified were:
    0 ≤ 1 + a
    -/
    have h_1_plus_a_not_neg : 1 + a ≥ 0 :=
      calc
        1 + a ≥ 1 + -1 := by rel [ha]
        /-
        Commenting out the line below gives this error on the last line (by extra)
        of the proof: unexpected token 'example'; expected ':='
        -/
        _ = 0 := by ring
    calc
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [IH]
      _ = 1 + k * a + a * (1 + k * a) := by ring
      _ = 1 + (k + 1) * a + a ^ 2 * k := by ring
      _ ≥ 1 + (k + 1) * a := by extra
    /-
    This proof doesn't need to be done using by_cases but doing so helped
    me get to the final form of the proof (the a < 0 case works for a ≥ 0 too)
    -/

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  · left
    numbers
  · obtain IHl | IHr := IH -- why does obtain ⟨c, IH⟩ := IH do somthing?
    · right
      obtain ⟨c, IH⟩ := IHl
      have IH' : 5 ^ k = 8 * c + 1 := by addarith [IH]
      have ht := calc
        5 ^ (k + 1) = 5 * 5 ^ k := by ring
        _ = 5 * (8 * c + 1) := by rw [IH']
      use 5 * c
      have ht2 := calc
        5 ^ (k + 1) = 5 * (8 * c + 1) := ht
        _ = 8 * (5 * c) + 5 := by ring
      addarith [ht2]
    · left
      obtain ⟨c, IH⟩ := IHr
      have IH' : 5 ^ k = 8 * c + 5 := by addarith [IH]
      have ht := calc
        5 ^ (k + 1) = 5 * 5 ^ k := by ring
        _ = 5 * (8 * c + 5) := by rw [IH']
        _ = 8 * (5 * c) + 25 := by ring
      have ht2 : 8 * (5 * c) ≡ 0 [ZMOD 8] := by
        use 5 * c
        ring
      have ht3 : 25 ≡ 1 [ZMOD 8] := by
        use 3
        ring
      have ht4 : 8 * (5 * c) + 25 ≡ 1 [ZMOD 8] := calc
        8 * (5 * c) + 25 ≡ 0 + 25 [ZMOD 8] := by rel [ht2]
        _ = 25 := by ring
        _ ≡ 1 [ZMOD 8] := by rel [ht3]
      obtain ⟨c2, h⟩ := ht4
      use c2
      calc
        5 ^ (k + 1) - 1 = 8 * (5 * c) + 25 - 1:= by rw [ht]
          _ = 8 * c2 := h

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  · left
    numbers
  · obtain IHl | IHr := IH
    · right
      obtain ⟨c, IH⟩ := IHl
      have IH' : 6 ^ k = 7 * c + 1 := by addarith [IH]
      have ht := calc
        6 ^ (k + 1) = 6 * 6 ^ k := by ring
        _ = 6 * (7 * c + 1) := by rw [IH']
        _ = 7 * (6 * c) + 6 := by ring
      use 6 * c
      addarith [ht]
    · left
      obtain ⟨c, IH⟩ := IHr
      have IH' : 6 ^ k = 7 * c + 6 := by addarith [IH]
      have ht := calc
        6 ^ (k + 1) = 6 * 6 ^ k := by ring
        _ = 6 * (7 * c + 6) := by rw [IH']
        _ = 7 * (6 * c) + 36 := by ring
        /-
      have ht2 : 7 * (6 * c) + 36 ≡ 1 [ZMOD 7] := calc
        7 * (6 * c) + 36 -/ _ ≡ 0 + 36 [ZMOD 7] := by extra
        _ = 36 := by ring
        _ ≡ 1 [ZMOD 7] := by
          use 5
          ring
      apply ht

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k HK
  · left
    use 0
    ring
  · obtain HK1 | HK2 | HK3 := HK
    · obtain ⟨c, h⟩ := HK1
      have h : 4 ^ k = 7 * c + 1 := by addarith [h]
      have ht := calc
        4 ^ (k + 1) = 4 * 4 ^ k := by ring
        _ = 4 * (7 * c + 1) := by rw [h]
        _ = 7 * (4 * c) + 4 := by ring
        _ ≡ 0 + 4 [ZMOD 7] := by extra
        _ = 4 := by ring
      right
      right
      apply ht
    · obtain ⟨c, h⟩ := HK2
      have h : 4 ^ k = 7 * c + 2 := by addarith [h]
      have ht := calc
        4 ^ (k + 1) = 4 * 4 ^ k := by ring
        _ = 4 * (7 * c + 2) := by rw [h]
        _ = 7 * (4 * c) + 8 := by ring
        _ ≡ 0 + 8 [ZMOD 7] := by extra
        _ = 8 := by ring
        _ ≡ 1 [ZMOD 7] := by
          use 1
          ring
      left
      apply ht
    · obtain ⟨c, h⟩ := HK3
      have h : 4 ^ k = 7 * c + 4 := by addarith [h]
      have ht := calc
        4 ^ (k + 1) = 4 * 4 ^ k := by ring
        _ = 4 * (7 * c + 4) := by rw [h]
        _ = 7 * (4 * c) + 16 := by ring
        _ ≡ 0 + 16 [ZMOD 7] := by extra
        _ = 16 := by ring
        _ ≡ 2 [ZMOD 7] := by
          use 2
          ring
      right
      left
      apply ht

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  sorry

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  sorry

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  sorry
