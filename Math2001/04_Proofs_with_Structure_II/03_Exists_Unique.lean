/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  sorry

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  intro h hy
  calc
    h = (4 * h - 3 + 3) / 4 := by ring
    _ = (9 + 3) / 4 := by rw [hy]
    _ = 3 := by ring

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro a
    extra
  intro y hy
  have ht : y ≤ 0 := by apply hy
  interval_cases y
  numbers

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  · constructor
    numbers
    constructor
    · numbers
    · use 3
      numbers
  · intro y h
    /- Instead of doing this, include h4 in the obtain statement like Example 4.3.4!
    obtain ⟨h1, h2, h3⟩ := h
    dsimp [Int.ModEq] at h3
    -/
    obtain ⟨h1, h2, k, h4⟩ := h
    /-
    obtain ⟨k, h3'⟩ := h3
    -/
    -- mod_cases h3 : y % 3
    -- interval_cases y
    /-
    This is where I got stuck before reading example 4.3.4
    -/
    have ht := calc
      11 - y > 11 - 3 := by rel [h2]
      _ > 3 * 2 := by numbers
    /-
    have :=
      3 * 2 < 11 - y := by
    -/
    have ht2 := calc
      3 * k = 11 - y := by rw [h4]
      _ > 3 * 2 := by rel [ht]
    cancel 3 at ht2
    have := calc
      11 - y ≤ 11 - 0 := by rel [h1]
      _ < 3 * 4 := by numbers
    have ht3 := calc
      3 * k = 11 - y := by rw [h4]
      _ < 3 * 4 := by rel [this]
    cancel 3 at ht3
    interval_cases k
    calc
      y = 11 - 9 := by addarith[h4]
