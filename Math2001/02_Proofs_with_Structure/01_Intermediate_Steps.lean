/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by addarith [h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by addarith [h3, h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h3 :=
  calc
    x ≤ 2 - 3 := by addarith [hx]
    _ = -1 := by ring
  calc
    y ≥ 3 - 2 * x := by addarith [hy]
    _ ≥ 3 - 2 * (-1) := by rel [h3]
    _ = 5 := by ring
    _ > 3 := by numbers

/-
/-
I struggled to get the correct syntax here until I noticed that example 2.1.3
uses two have clauses but stated them differently. I used the format from that
example to get lean to recognize my statement of h4.
-/
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 :=
  calc
    0 ≤ a + b := by addarith [h1]
    _ = b + a := by ring
  have h4 :=
  calc
    0 ≤ b - a := by addarith [h2]
  calc
    a ^ 2 ≤ a^2 + (b + a) * (b - a) := by addarith [h3, h4]
    _ = b * b := by ring
    _ = b^2 := by extra
-/

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 :=
  calc
    0 ≤ a + b := by addarith [h1]
    _ = b + a := by ring
  have h4 : 0 ≤ b - a := by addarith [h2]
  calc
    a ^ 2 ≤ a^2 + ((b + a) * (b - a)) := by extra
    -- the next line is not needed but I left in here to show that
    -- lean doesn't consider the proof complete without final line
    _ = b * b := by ring
    _ = b^2 := by ring

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  sorry

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  sorry

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  sorry

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  sorry
