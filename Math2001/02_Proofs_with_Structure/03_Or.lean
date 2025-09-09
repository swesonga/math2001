/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    n^2 = n * n := by ring
    _ ≥ 2 * 2 := by rel [hn]
    _ = 4 := by ring
    _ > 2 := by numbers

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hl | hr := h2
  left
  calc
    x = (x - 1) + 1 := by ring
    _ = 0 + 1 := by rw [hl]
    _ = 1 := by ring
  right
  calc
    x = (x - 2) + 2 := by ring
    _ = 0 + 2 := by rw [hr]
    _ = 2 := by ring

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hx | hx := h
  calc
    x^2 + 1 = 4^2 + 1 := by rw [hx]
    _ = 17 := by ring
  calc
    x^2 + 1 = (-4)^2 + 1 := by rw [hx]
    _ = 17 := by ring

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain hx | hx := h
  calc
    x^2 - 3 * x + 2 = 1^2 - 3 * 1 + 2 := by rw [hx]
    _ = 0 := by ring
  calc
    x^2 - 3 * x + 2 = 2^2 - 3 * 2 + 2 := by rw [hx]
    _ = 0 := by ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain ht | ht := h
  calc
    t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [ht]
    _ = 0 := by ring
  calc
    t ^ 2 - t - 6 = (3) ^ 2 - (3) - 6 := by rw [ht]
    _ = 0 := by ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  calc
    x * y + 2 * x = 2 * y + 2 * 2 := by rw [hx]
    _ = 2 * y + 4 := by ring
  calc
    x * y + 2 * x = x * -2 + 2 * x := by rw [hy]
--    _ = 0 := by ring
    _ = 2 * (-2) + 4 := by ring
    _ = 2 * y + 4 := by rw [hy]

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t = 3 - t + t := by rw [h]
    _ = 3 := by ring

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  --have h1 : 2 * b < -a := by addarith [h]
  --have h2 : b < -a / 2 := by addarith [h]
  calc
    b < -a / 2 := by addarith [h]

/-
I had to step back and try a different approach after frustration with
not being able to show that y - 1 < y, which seems true for any real number y
-/
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  -- have h1 : x = (y - 1)/2 := by addarith [h]
  -- have h2 : 0 < 1/2 := by numbers
  -- have h3: y - 1 < y := by extra
  have h4:=
    calc
     y = 2 * x + 1 := h
     _ > 2 * x := by extra
  calc
    x < y / 2 := by addarith [h4]
  /-
    x = (y - 1)/2 := by addarith [h]
--    _ = y/2 - 1/2 := by addarith [h]
    _ < (y - 1 + 1)/2 := by numbers
--    x = (y - 1)/2 := by addarith [h]
--    _ = (2 * x + 1 - 1)/2 := by rw [h]
  -/

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 :=
    calc (x + 3) * (x - 1) = x ^ 2 + 2 * x - 3 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hxl | hxr := h2
  left
  calc
    x = x + 3 - 3 := by ring
    _ = 0 - 3 := by rw [hxl]
    _ = -3 := by ring
  right
  calc
    x = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [hxr]
    _ = 1 := by ring

/-
Don't know why it took me a while to see that a = b ∨ a = 2 * b is just saying
a - b = 0 ∨ a - 2 * b = 0
-/
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
/-
  have h1: a ^ 2 + 2 * b ^ 2 - 3 * a * b = 0 := by addarith [hab]
  --have h2: a ^ 2 + 2 * b ^ 2 ≥ 0 := by addarith [hab]
  --have h3: a * b ≥ 0 := by addarith [hab]
-/
  have h1: a ^ 2 + 2 * b ^ 2 - 3 * a * b = 0 := by addarith [hab]
  have h2 :=
    calc
      (a - b) * (a - 2 * b) = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
      _ = 0 := by rw [h1]
  have h := eq_zero_or_eq_zero_of_mul_eq_zero h2
  obtain hl | hr := h
  · left
    calc
      a = a - b + b := by ring
      _ = 0 + b := by rw [hl]
      _ = b := by ring
  · right
    calc
      -- shorter than expanding it out as done for the left case above
      a = 2 * b := by addarith [hr]


example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 :=
    calc
      t ^ 3 - t ^ 2 = t ^ 3 - t ^ 3 := by rw [ht]
      _ = 0 := by ring
  -- cancel t at h1
  /-
  --Why doesn't this work?
  have h2 :=
    calc
      t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
  -/
--  have h3: t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
  have h3:=
    calc
     t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
     _ = 0 := by rw [h1]
  -- have h4: t ^ 2 * (t - 1) = 0 := by rw [h1]
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  obtain htz | ht1 := h5
  · right
    cancel 2 at htz
  · left
    calc
      t = t - 1 + 1 := by ring
      _ = 0 + 1 := by rw [ht1]
      _ = 1 := by ring

example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hn := le_or_succ_le n 2
  obtain hn2 | hn3 := hn
  apply ne_of_lt
  calc
    n^2 = n * n := by ring
    _ ≤ 2 * 2 := by rel [hn2]
    _ = 4 := by ring
    _ < 7 := by numbers
  apply ne_of_gt
  calc
    7 < 9 := by numbers
    _ = 3 * 3 := by ring
    _ ≤ n * n := by rel [hn3]
    _ = n^2 := by ring
  /-
    -- why doesn't this work?
    n^2 = n * n := by ring
    _ ≤ 3 * 3 := by rel [hn2]
    _ = 9 := by ring
    _ > 7 := by numbers
  -/

/-
example {x : ℤ} : 2 * x ≠ 3 := by
  -- have h := le_or_succ_le (2 * x) 3
  have h := le_or_succ_le (2 * x) 2
  -- have hx := le_or_succ_le x 1
  obtain hle | hgt := h
  · apply ne_of_lt
/-
    have h1 :=
      calc
        x = 2 * x - x := by ring
        _ ≤ 3 - x := by rel [hle]
-/
    calc
      2 * x ≤ 2 := hle
      _ < 3 := by numbers
  · apply ne_of_gt
/-
    have hx := le_or_succ_le x 1
    · obtain hxl | hxr := hx
      · calc
          3 ≤ 2 * x := hgt
          _ ≤ 2 * 1 := by rel [hxl]
          _ = 2 := by ring
-/
-/

example {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain hle | hgt := hx
  · apply ne_of_lt
    calc
      2 * x = x + x := by ring
      _ ≤ 1 + 1 := by rel [hle]
      _ = 2 := by ring
      _ < 3 := by numbers
    /-
      x = 2 * x - x := by ring
      _ ≤ 2 * 1 - 1 := by rel [hle]
      -- 2 * x ≤ 2 := by addarith [hle]
      _ < 3 := by numbers
    -/
  · apply ne_of_gt
    -- have h: 2 * 2 ≤ 2 * x := by addarith [hgt]
    have h: 2 * 2 ≤ 2 * x := by rel [hgt]
    /-
    Why does this calc block fail while being similar to hypothesis h above?
    calc
      3 < 4 := by numbers
      _ = 2 * 2 := by ring
      _ ≤ 2 * x := by rel [hgt]
    -/
    calc
      4 = 2 * 2 := by ring
      _ ≤ 2 * x := by rel [h]
    /-
    -- alternatively:
    calc
      2 * x ≥ 2 * 2 := by rel [h]
      _ = 4 := by ring
    -/

example {t : ℤ} : 5 * t ≠ 18 := by
  have ht := le_or_succ_le t 3
  obtain htle3 | h4let := ht
  · apply ne_of_lt
    calc
      5 * t ≤ 5 * 3 := by rel [htle3]
      _ = 15 := by ring
      _ < 18 := by numbers
  · apply ne_of_gt
    calc
      5 * t ≥ 5 * 4 := by rel [h4let]
      _ = 20 := by ring
      _ > 18 := by numbers

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm := le_or_succ_le m 5
  obtain hmle5 | h6lem := hm
  · apply ne_of_lt
    calc
      m^2 + 4 * m ≤ 5^2 + 4 * 5 := by rel [hmle5]
      _ = 45 := by ring
      _ < 46 := by numbers
  · apply ne_of_gt
    calc
      m^2 + 4 * m ≥ 6^2 + 4 * 6 := by rel [h6lem]
      _ = 60 := by ring
      _ > 46 := by numbers
