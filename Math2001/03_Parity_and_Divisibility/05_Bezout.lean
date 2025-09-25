/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, h⟩ := hn
  dsimp [(· ∣ · )]
  have ht := calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [h]
    _ = 8 * (5 * a - 3 * n) := by ring
  use 5 * a - 3 * n
  apply ht

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨k, h⟩ := h1
  dsimp [(· ∣ · )]
  have ht := calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * k) - 5 * n := by rw [h]
    _ = 5 * (2 * k - n) := by ring
  use 2 * k - n
  apply ht

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/

/-
saw these solutions right away after finishing the section 4.1
exercises. Most likely solving 4.1.10. Exercise #2 made this easy
-/
example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨k, h⟩ := hn
  dsimp [(· ∣ · )]
  /-
  have ht := calc
    n = 2 * (3 * n) - 5 * n := by ring
  -/
  have h1 := calc
    n = 12 * n - 11 * n := by ring
    _ = 12 * n - 6 * k := by rw [h]
    _ = 6 * (2 * n - k) := by ring
  use 2 * n - k
  apply h1

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨ k, ha'⟩ := ha
  dsimp [(· ∣ · )]
  have h1 := calc
    a = 15 * a - 14 * a := by ring
    _ = 3 * (5 * a) - 14 * a := by ring
    _ = 3 * (7 * k) - 14 * a := by rw [ha']
    _ = 7 * (3 * k - 2 * a) := by ring
  use 3 * k - 2 * a
  apply h1

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨k7, h7⟩ := h1
  obtain ⟨k9, h9⟩ := h2
  have ht := calc
    n = 28 * n - 27 * n := by ring
    _ = 28 * (9 * k9) - 27 * n := by rw [h9]
    _ = 28 * (9 * k9) - 27 * (7 * k7) := by rw [h7]
    _ = 63 * (4 * k9 - 3 * k7) := by ring
  use 4 * k9 - 3 * k7
  apply ht

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨k5, h5⟩ := h1
  obtain ⟨k13, h13⟩ := h2
  have ht := calc
    n = 26 * n - 25 * n := by ring
    _ = 26 * (5 * k5) - 25 * n := by rw [h5]
    _ = 26 * (5 * k5) - 25 * (13 * k13) := by rw [h13]
    _ = 65 * (2 * k5 - 5 * k13) := by ring
  use 2 * k5 - 5 * k13
  apply ht
