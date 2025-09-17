/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp [(· ∣ ·)]
  use -3
  numbers

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨k1, hk1⟩ := hab
  obtain ⟨k2, hk2⟩ := hbc
  have ht := calc
    c = b^2 * k2 := hk2
    _ = (a * k1) ^ 2 * k2 := by rw [hk1]
    _ = a^2 * (k1 ^ 2 * k2) := by ring
  dsimp [(· ∣ ·)]
  use k1 ^ 2 * k2
  apply ht

example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨k1, hk1⟩ := h
  dsimp [(· ∣ ·)]
  use y * k1
  calc
    z = x * y * k1 := hk1
    _ = x * (y * k1) := by ring

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hk⟩ := hab
  have ht := calc
    0 < b := hb
    _ = a * k := hk
  cancel k at ht

/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  dsimp [(· ∣ ·)]
  use 0
  calc
    0 = t * 0 := by ring

example : ¬(3 : ℤ) ∣ -10 := by
  dsimp [(· ∣ ·)]
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  · numbers
  · numbers

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hxy⟩ := h
  dsimp [(· ∣ · )]
  have ht := calc
    3 * y - 4 * y ^ 2 = 3 * (x * k) - 4 * (x * k)^2 := by rw [hxy]
    _ = x * (3 * k - 4 * x * k^2) := by ring
  use 3 * k - 4 * x * k^2
  apply ht

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hmn⟩ := h
  dsimp [(· ∣ · )]
  have ht := calc
    2 * n ^ 3 + n = 2 * (m * k) ^ 3 + m * k := by rw [hmn]
    _ = m * (2 * m^2 * k^3 + k) := by ring
  use 2 * m^2 * k^3 + k
  apply ht

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hab'⟩ := hab
  dsimp [(· ∣ · )]
  have ht := calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw [hab']
    _ = a * (2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k) := by ring
  use 2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k
  apply ht

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨k1, hkl⟩ := h1
  obtain ⟨k2, hlm⟩ := h2
  dsimp [(· ∣ · )]
  have ht := calc
    m = l ^ 3 * k2 := hlm
    _ = (k * k1) ^ 3 * k2 := by rw [hkl]
    _ = k ^ 3 * (k1 ^ 3 * k2) := by ring
  use k1 ^ 3 * k2
  apply ht

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨k1, hpq'⟩ := hpq
  obtain ⟨k2, hqr'⟩ := hqr
  have ht := calc
    r = q ^ 2 * k2 := hqr'
    _ = (p ^ 3 * k1) ^ 2 * k2 := by rw [hpq']
    _ = p ^ 6 * (k1 ^ 2 * k2) := by ring
  use k1 ^ 2 * k2
  apply ht

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  · numbers
  · dsimp [(· ∣ · )]
    use 7
    numbers

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 5, 3
  constructor
  · numbers
  · constructor
    · numbers
    · dsimp [(· ∣ · )]
      use 4
      numbers
