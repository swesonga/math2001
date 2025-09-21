/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  rel [ha]


example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel [hb]
    _ = 2 + 5 * 8 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra


example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] := by
  use 8
  calc
    (6:ℤ) * 8 = 4 + 4 * 11 := by numbers
    _ ≡ 4 [ZMOD 11] := by extra


example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

/-! # Exercises -/


-- I used the ChatGPT prompt "factor n^3-1"
example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by
  /-
  --apply Int.ModEq.pow_three
  obtain ⟨k, hn'⟩ := hn
  have ht : n ^ 3 ≡ 1 [ZMOD 3] := by
    dsimp [Int.ModEq] at *
    -- apply Int.ModEq.pow_three
    /-
    calc
      n ^ 3 - 1 = (n - 1) * (n ^ 2 + n + 1) := by ring
      _ = 3 * k * (n ^ 2 + n + 1) := by rw [hn']
    -/
    -- calc block above gives us value to use
    use k * (n ^ 2 + n + 1)
    calc
      n ^ 3 - 1 = (n - 1) * (n ^ 2 + n + 1) := by ring
      _ = 3 * k * (n ^ 2 + n + 1) := by rw [hn']
  have ht2 : 7 * n ≡ 1 [ZMOD 3] := by
  -/
  dsimp [Int.ModEq] at *
  dsimp [(· ∣ .)] at *
  obtain ⟨k, hn'⟩ := hn
  --have ht : 3 | 7 * n - 1 := by
  /-
  calc
    7 * n - 1 = 7 * (n - 1) + 6 := by ring
  -/
  use (k * (n ^ 2 + n + 1)) + (7 * k + 2)
  calc
    n ^ 3 + 7 * n - 2 = (n ^ 3 - 1) + (7 * n - 1) := by ring
    _ = (n - 1) * (n ^ 2 + n + 1) + 7 * (n - 1) + 6 := by ring
    _ = 3 * k * (n ^ 2 + n + 1) + 7 * (3 * k) + 6 := by rw [hn']
    _ = 3 * (k * (n ^ 2 + n + 1) + 7 * k + 2) := by ring
  ring

example {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] := by
  obtain ⟨k, ha'⟩ := ha
  have ht1 : a = 4 * k + 3 := by addarith [ha']
  have ht := calc
    a ^ 3 + 4 * a ^ 2 + 2 = (4 * k + 3) ^ 3 + 4 * (4 * k + 3) ^ 2 + 2 := by rw [ht1]
    -- used chatgpt.com to expand this. it used the binomial expansion formula (a+b)^3 = a^3+3a^2b+3ab^2+b^3
    _ = (64 * k ^ 3 + 144 * k ^ 2 + 108 * k + 27) + 4 * (16 * k ^ 2 + 24 * k + 9) + 2 := by ring
    _ = 64 * k ^ 3 + 208 * k ^ 2 + 204 * k + 65 := by ring
    _ = 4 * (16 * k ^ 3 + 52 * k ^ 2 + 51 * k + 16) + 1 := by ring
  use 16 * k ^ 3 + 52 * k ^ 2 + 51 * k + 16
  calc
    a ^ 3 + 4 * a ^ 2 + 2 - 1 = 4 * (16 * k ^ 3 + 52 * k ^ 2 + 51 * k + 16) + 1 - 1 := by rw [ht]
    _ = 4 * (16 * k ^ 3 + 52 * k ^ 2 + 51 * k + 16) := by ring

example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] := by
  have ht: (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by ring
  use a ^ 2 * b + a * b ^ 2
  calc
    (a + b) ^ 3 - (a ^ 3 + b ^ 3) =
      a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 - (a ^ 3 + b ^ 3) := by ring
    _ = 3 * a ^ 2 * b + 3 * a * b ^ 2 := by ring
    _ = 3 * (a ^ 2 * b + a * b ^ 2) := by ring

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 9
  use 5
  numbers

example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  use 6
  use 3
  numbers

example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases h : n % 2
  · obtain ⟨k, hn⟩ := h
    have ht : n = 2 * k := by addarith [hn]
    have ht2 := calc
      5 * n ^ 2 + 3 * n + 7 - 1 = 5 * (2 * k) ^ 2 + 3 * (2 * k) + 7 - 1:= by rw [ht]
      _ = 2 * (10 * k ^ 2 + 3 * k + 3) := by ring
    use (10 * k ^ 2 + 3 * k + 3)
    apply ht2
  · obtain ⟨k, hn⟩ := h
    have ht : n = 2 * k + 1 := by addarith [hn]
    have ht2 := calc
      5 * n ^ 2 + 3 * n + 7 - 1 = 5 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 7 - 1 := by rw [ht]
      _ = 5 * (4 * k ^ 2 + 4 * k + 1) + 6 * k + 3 + 6 := by ring
      _ = 2 * (10 * k ^ 2 + 13 * k + 7) := by ring
    use (10 * k ^ 2 + 13 * k + 7)
    apply ht2

/-
See shorter proof of this in the next example (line 196)
-/
example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases h : x % 5
  /-
  dsimp [Int.ModEq] at *
  dsimp [(· ∣ · )] at *
  apply Int.ModEq.pow_three
  -/
  · obtain ⟨k, hx⟩ := h
    have ht : x = 5 * k := by addarith [hx]
    have ht2 := calc
      x ^ 5 = (5 * k) ^ 5 := by rw [ht]
      _ = 5 * 5 ^ 4 * k ^ 5 := by ring
    dsimp [Int.ModEq] at *
    use 5 ^ 4 * k ^ 5 - k
    calc
      x ^ 5 - x = (5 * 5 ^ 4 * k ^ 5) - (5 * k) := by rw [ht2, ht]
      _ = 5 * (5 ^ 4 * k ^ 5 - k) := by ring
  · obtain ⟨k, hx⟩ := h
    have ht : x = 5 * k + 1 := by addarith [hx]
    have ht2 := calc
      x ^ 5 - x = (5 * k + 1) ^ 5 - (5 * k + 1):= by rw [ht]
      -- use binomial theorem
      _ = 3125 * k ^ 5 + 3125 * k^4 + 1250 * k^3 + 250 * k^2 + 25 * k + 1 - (5 * k + 1) := by ring
      _ = 5 * (625 * k ^ 5 + 625 * k^4 + 250 * k^3 + 50 * k^2 + 4 * k) := by ring
    use 625 * k ^ 5 + 625 * k^4 + 250 * k^3 + 50 * k^2 + 4 * k
    apply ht2
  · obtain ⟨k, hx⟩ := h
    have ht : x = 5 * k + 2 := by addarith [hx]
    have ht2 := calc
      x ^ 5 - x = (5 * k + 2) ^ 5 - (5 * k + 2):= by rw [ht]
      -- use binomial theorem. chatgpt did not expand this correctly the first time
      _ = 3125 * k ^ 5 + 6250 * k^4 + 5000 * k^3 + 2000 * k^2 + 400 * k + 32 - (5 * k + 2) := by ring
      _ = 5 * (625 * k ^ 5 + 1250 * k^4 + 1000 * k^3 + 400 * k^2 + 79 * k + 6) := by ring
    use 625 * k ^ 5 + 1250 * k^4 + 1000 * k^3 + 400 * k^2 + 79 * k + 6
    apply ht2
  · obtain ⟨k, hx⟩ := h
    have ht : x = 5 * k + 3 := by addarith [hx]
    have ht2 := calc
      x ^ 5 - x = (5 * k + 3) ^ 5 - (5 * k + 3):= by rw [ht]
      -- use binomial theorem
      _ = 3125 * k ^ 5 + 9375 * k^4 + 11250 * k^3 + 6750 * k^2 + 2025 * k + 243 - (5 * k + 3) := by ring
      _ = 5 * (625 * k ^ 5 + 1875 * k^4 + 2250 * k^3 + 1350 * k^2 + 404 * k + 48) := by ring
    use 625 * k ^ 5 + 1875 * k^4 + 2250 * k^3 + 1350 * k^2 + 404 * k + 48
    apply ht2
  · obtain ⟨k, hx⟩ := h
    have ht : x = 5 * k + 4 := by addarith [hx]
    have ht2 := calc
      x ^ 5 - x = (5 * k + 4) ^ 5 - (5 * k + 4):= by rw [ht]
      -- use binomial theorem
      _ = 3125 * k ^ 5 + 12500 * k^4 + 20000 * k^3 + 16000 * k^2 + 6400 * k + 1024 - (5 * k + 4) := by ring
      _ = 5 * (625 * k ^ 5 + 2500 * k^4 + 4000 * k^3 + 3200 * k^2 + 1279 * k + 204) := by ring
    use 625 * k ^ 5 + 2500 * k^4 + 4000 * k^3 + 3200 * k^2 + 1279 * k + 204
    apply ht2

/-
Shorter proof of last example above
-/
example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5
  calc
    x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 32 := by numbers
    _ ≡ 2 [ZMOD 5] := by
      use 6
      numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 243 := by numbers
    _ ≡ 3 [ZMOD 5] := by
      use 48
      numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 1024 := by numbers
    _ ≡ 4 [ZMOD 5] := by
      use 204
      numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
