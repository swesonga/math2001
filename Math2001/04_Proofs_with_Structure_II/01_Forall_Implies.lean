/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers


example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2


example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h2 : (a + b)/2 ≥ a ∨ (a + b)/2 ≤ b := by apply h
  obtain hl | hr := h2
  · calc
      b = 2 * ((a + b)/2) - a := by ring -- need the extra parens for the rel [hl] on the next line
      _ ≥ 2 * a - a := by rel [hl]
      _ = a := by ring
  · calc
      a = 2 * ((a + b)/2) - b := by ring
      _ ≤ 2 * b - b := by rel [hr]
      _ = b := by ring

example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring


example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  /-
  use -4
  intro x y h
  have hxsq := calc
    x ^ 2 ≤ 4 - y ^ 2 := by addarith [h]
    _ ≤ 4 - 0 := by extra
    _ = 2 ^ 2 := by numbers
  have hysq := calc
    y ^ 2 ≤ 4 - x ^ 2 := by addarith [h]
    _ ≤ 4 - 0 := by extra
    _ = 2 ^ 2 := by numbers
  have hx := by apply abs_le_of_sq_le_sq hxsq
  -/
  use -3
  intro x y h
  have ht := calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y)^2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ 3 ^ 2 := by numbers
  have h3 : (0 : ℝ) ≤ 3 := by numbers -- use the reals to avoid error on line 76
  have hu : -3 ≤ (x + y) ∧ (x + y) ≤ 3
     := by apply abs_le_of_sq_le_sq' ht h3
     /-
     application type mismatch
  abs_le_of_sq_le_sq' ht h3
argument
  h3
has type
  @OfNat.ofNat ℕ 0 (instOfNatNat 0) ≤ 3 : Prop
but is expected to have type
  @OfNat.ofNat ℝ 0 Zero.toOfNat0 ≤ 3 : Prop
     -/
  /-
  see cryptic error message if this one is used
  -- obtain hl | hr := hu
  -/
  obtain ⟨h1, h2⟩ := hu
  apply h1

example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp
  use 5
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra


example : Prime 2 := by
  constructor
  · numbers -- show `2 ≤ 2`
  intro m hmp
  have hp : 0 < 2 := by numbers
  have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
  interval_cases m
  · left
    numbers -- show `1 = 1`
  · right
    numbers -- show `2 = 2`


example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- show `2 ≠ 1`
  · numbers -- show `2 ≠ 6`
  · numbers -- show `6 = 2 * 3`

/-! # Exercises -/


example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  sorry

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry

example : ¬(Prime 45) := by
  sorry
