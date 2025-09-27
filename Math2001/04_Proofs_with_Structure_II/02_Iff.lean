/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Int.ModEq] at *
    obtain ⟨k, hk⟩ := h
    dsimp [Odd] at *
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Int.ModEq] at h
    dsimp [(· ∣ ·)] at h
    dsimp [Even]
    obtain ⟨c, h'⟩ := h
    use c
    addarith [h']

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h2 := calc
      (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
      _ = 0 := h
    -- found this lemma in example 2.3.4
    have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
    obtain hl | hr := h3
    · left
      addarith [hl]
    · right
      addarith [hr]
  · intro h
    obtain hl | hr := h
    calc
      x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [hl]
      _ = 0 := by ring
    calc
      x ^ 2 + x - 6 = (2) ^ 2 + (2) - 6 := by rw [hr]
      _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    /-
    have h1 := calc
      (a - 2) * (a - 3) = a ^ 2 - 5 * a + 6 := by ring
      _ ≤ 0 := by addarith [h]
    -- interval_cases a -- interval_cases failed: could not find bounds on a
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    -/
    -- I couldn't come up with the rewriting the example uses in the text on my own
    have h1 := calc
      (2 * a - 5) ^ 2 = 4 * a ^ 2 - 20 * a + 25 := by ring
      _ = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * (-1) + 5 := by rel [h]
      _ = 1 ^ 2 := by ring -- must be ^2 to apply abs_le_of_sq_le_sq' from 2.4
    have h2 : -1 ≤ (2 * a - 5) ∧ (2 * a - 5) ≤ 1 := by
      apply abs_le_of_sq_le_sq' h1
      numbers
    obtain ⟨hl, hr⟩ := h2
    have hl2 : 2 * 2 ≤ 2 * a := by addarith [hl]
    have hr2 : 2 * a ≤ 2 * 3 := by addarith [hr]
    -- took a bit of effort to remember how this was done. Rereading the
    -- sentence in 4.2.6. Example starting with this bit helped:
    -- Therefore 2 * 2 ≤ 2a, so 2 ≤ a
    cancel 2 at hl2
    cancel 2 at hr2
    interval_cases a
    · left
      numbers
    · right
      numbers
  · intro h
    obtain hl | hr := h
    · calc
        a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw [hl]
        _ = -1 := by ring
        _ ≤ -1 := by numbers
    . calc
        a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw [hr]
        _ = -1 := by ring
        _ ≤ -1 := by numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  dsimp [Even]
  obtain hl | hr := hn2
  · use 2
    calc
      n = 4 := by addarith [hl]
      _ = 2 * 2 := by ring
  · use 3
    calc
      n = 6 := by addarith [hr]
      _ = 2 * 3 := by ring

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  dsimp [Even]
  obtain hl | hr := hn1
  · use 2
    calc
      n = 4 := by addarith [hl]
      _ = 2 * 2 := by ring
  · use 3
    calc
      n = 6 := by addarith [hr]
      _ = 2 * 3 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  sorry

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  sorry

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  sorry

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  sorry

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  sorry
