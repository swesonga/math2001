/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨ k, hk⟩ := hn
  have ht :=
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 14 * k + 7 - 4 := by ring
    _ = 14 * k + 2 + 1 := by ring
    _ = 2 * (7 * k + 1) + 1 := by ring
  use 7 * k + 1
  apply ht

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨k1, hx'⟩ := hx
  obtain ⟨k2, hy'⟩ := hy
  have ht :=
    calc
      x * y + 2 * y = (2 * k1 + 1) * (2 * k2 + 1) + 2 * (2 * k2 + 1) := by rw [hx', hy']
      _ = 2 * k1 * 2 * k2 + 2 * k1 + (2 * k2 + 1) + 4 * k2 + 2 := by ring
      _ = 4 * k1 * k2 + 2 * k1 + 6 * k2 + 3 := by ring
      _ = 2 * (2 * k1 * k2 + k1 + 3 * k2 + 1) + 1 := by ring
  use 2 * k1 * k2 + k1 + 3 * k2 + 1
  apply ht

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  dsimp [Odd] at *
  dsimp [Even] at *
  obtain ⟨m1, hm'⟩ := hm
  have ht :=
    calc
      3 * m - 5 = 3 * (2 * m1 + 1) - 5 := by rw [hm']
      _ = 6 * m1 + 3 - 5 := by ring
      _ = 2 * (3 * m1 - 1) := by ring
  use 3 * m1 - 1
  apply ht

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨n1, hn'⟩ := hn
  have hnt :=
    calc
      n^2 + 2 * n - 5 = (2 * n1)^2 + 2 * (2 * n1) - 5 := by rw [hn']
      _ = 4 * n1^2 + 4 * n1 - 5 := by ring
      _ = 2 * (2 * n1^2 + 2 * n1 - 3) + 1 := by ring
  use 2 * n1^2 + 2 * n1 - 3
  apply hnt


example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd, Even] at *
  obtain ⟨m1, hm'⟩ := hm
  obtain ⟨n1, hn'⟩ := hn
  have ht := calc
    n + m = 2 * n1 + (2 * m1 + 1) := by rw [hm', hn']
    _ = 2 * (n1 + m1) + 1 := by ring
  use n1 + m1
  apply ht

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd, Even] at *
  obtain ⟨p1, hp'⟩ := hp
  obtain ⟨q1, hq'⟩ := hq
  have ht := calc
    p - q - 4 = 2 * p1 + 1 - 2 * q1 - 4 := by rw [hp', hq']
    _ = 2 * (p1 - q1 - 2) + 1 := by ring
  use p1 - q1 - 2
  apply ht

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  dsimp [Odd, Even] at *
  obtain ⟨a1, ha'⟩ := ha
  obtain ⟨b1, hb'⟩ := hb
  have ht := calc
    3 * a + b - 3 = 3 * (2 * a1) + (2 * b1 + 1) - 3 := by rw [ha', hb']
    _ = 2 * (3 * a1) + (2 * b1 + 1) - 3 := by ring
    _ = 2 * (3 * a1 + b1 - 1) := by ring
  use 3 * a1 + b1 - 1
  apply ht

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  dsimp [Odd, Even] at *
  obtain ⟨r1, hr'⟩ := hr
  obtain ⟨s1, hs'⟩ := hs
  have ht := calc
    3 * r - 5 * s = 3 * (2 * r1 + 1) - 5 * (2 * s1 + 1) := by rw [hr', hs']
    _ = 2 * 3 * r1 + 3 - 2 * 5 * s1 - 5 := by ring
    _ = 2 * (3 * r1 - 5 * s1 - 1) := by ring
  use 3 * r1 - 5 * s1 - 1
  apply ht

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at *
  obtain ⟨m, hx'⟩ := hx
  have ht := calc
    x^3 = (2 * m + 1)^3 := by rw [hx']
    _ = (2 * m + 1) * (2 * m + 1)^2 := by ring
    _ = (2 * m + 1) * (4 * m^2 + 4 * m + 1) := by ring
    _ = (2 * m + 1) * (4 * m^2 + 4 * m + 1) := by ring
    _ = (8 * m^3 + 8 * m^2 + 2*m) + (4 * m^2 + 4 * m + 1) := by ring
    _ = 8 * m^3 + 12 * m^2 + 6 * m + 1 := by ring
    _ = 2 * (4 * m^3 + 6 * m^2 + 3 * m) + 1 := by ring
  use (4 * m^3 + 6 * m^2 + 3 * m)
  apply ht

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Odd, Even] at *
  obtain ⟨m, hn'⟩ := hn
  have ht := calc
    n ^ 2 - 3 * n + 2 = (2 * m + 1) ^ 2 - 3 * (2 * m + 1) + 2 := by rw [hn']
    _ = (4 * m^2 + 4 * m + 1) - 3 * (2 * m + 1) + 2 := by ring
    _ = (4 * m^2 - 2 * m) := by ring
    _ = 2 * (2 * m^2 - m) := by ring
  use 2 * m^2 - m
  apply ht

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at *
  obtain ⟨m, ha'⟩ := ha
  have ht := calc
    a ^ 2 + 2 * a - 4 = (2 * m + 1) ^ 2 + 2 * (2 * m + 1) - 4 := by rw [ha']
    _ = (4 * m^2 + 4 * m + 1) + 2 * (2 * m + 1) - 4 := by ring
    _ = (4 * m^2 + 8 * m - 1) := by ring
    _ = 2 * (2 * m^2 + 4 * m - 1) + 1 := by ring
  use 2 * m^2 + 4 * m - 1
  apply ht

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at *
  obtain ⟨m, hp'⟩ := hp
  have ht := calc
    p ^ 2 + 3 * p - 5 = (2 * m + 1) ^ 2 + 3 * (2 * m + 1) - 5 := by rw [hp']
    _ = (4 * m^2 + 4 * m + 1) + 3 * (2 * m + 1) - 5 := by ring
    _ = (4 * m^2 + 10 * m - 1) := by ring
    _ = 2 * (2 * m^2 + 5 * m - 1) + 1 := by ring
  use 2 * m^2 + 5 * m - 1
  apply ht

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Odd] at *
  obtain ⟨k1, hx'⟩ := hx
  obtain ⟨k2, hy'⟩ := hy
  have ht := calc
    x * y = (2 * k1 + 1) * (2 * k2 + 1) := by rw [hx', hy']
    _ = 4 * k1 * k2 + 2 * k1 + 2 * k2 + 1 := by ring
    _ = 2 * (2 * k1 * k2 + k1 + k2) + 1 := by ring
  use 2 * k1 * k2 + k1 + k2
  apply ht

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn | hn := Int.even_or_odd n -- switch on whether n is odd or even
  dsimp [Odd, Even] at *
  · obtain ⟨k1, hn'⟩ := hn
    have ht := calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k1) ^ 2 + 3 * (2 * k1) - 1 := by rw [hn']
      _ = 2 * 6 * k1 ^ 2 + 3 * (2 * k1) - 1 := by ring
      _ = 2 * (6 * k1 ^ 2 + 3 * k1 - 1) + 1 := by ring
    use 6 * k1 ^ 2 + 3 * k1 - 1
    apply ht
  · obtain ⟨k1, hn'⟩ := hn
    have ht := calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k1 + 1) ^ 2 + 3 * (2 * k1 + 1) - 1 := by rw [hn']
      _ = 3 * (4 * k1 ^ 2 + 4 * k1 + 1) + 6 * k1 + 3 - 1 := by ring
      _ = 2 * (6 * k1 ^ 2 + 9 * k1 + 2) + 1 := by ring
    use 6 * k1 ^ 2 + 9 * k1 + 2
    apply ht

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn | hn := Int.even_or_odd n -- switch on whether n is odd or even
  · dsimp [Odd, Even] at *
    obtain ⟨k, hn'⟩ := hn
    use 2 * k + 1
    constructor
    · calc
        2 * k + 1 ≥ 2 * k := by extra
        _ = n := by rw [hn']
    · use k
      /-
      have ht := calc
        2 * k + 1 = 2 * k + 1 := by ring
      -/
      ring
  · dsimp [Odd] at *
    use n
    constructor
    · extra
    · obtain ⟨k, hn'⟩ := hn
      use k
      apply hn'

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  obtain hb | hb := Int.even_or_odd b
  -- Even a ∧ Even b
  · left
    dsimp [Even] at *
    obtain ⟨ka, ha'⟩ := ha
    obtain ⟨kb, hb'⟩ := hb
    have ht := calc
      a - b = 2 * ka - 2 * kb := by rw [ha', hb']
      _ = 2 * (ka - kb) := by ring
    use ka - kb
    apply ht
  -- Even a ∧ Odd b
  · obtain hc | hc := Int.even_or_odd c
    -- Even a ∧ Odd b ∧ Even c
    · right
      left
      dsimp [Even] at *
      obtain ⟨ka, ha'⟩ := ha
      obtain ⟨kc, hc'⟩ := hc
      use ka + kc
      calc
        a + c = 2 * ka + 2 * kc := by rw [ha', hc']
        _ = 2 * (ka + kc) := by ring
    -- Even a ∧ Odd b ∧ Odd c
    · right
      right
      dsimp [Even, Odd] at *
      obtain ⟨kb, hb'⟩ := hb
      obtain ⟨kc, hc'⟩ := hc
      have ht :=
        calc
          b - c = 2 * kb + 1 - (2 * kc + 1) := by rw [hb', hc']
          _ = 2 * (kb - kc) := by ring
      use kb - kc
      apply ht
  -- Odd a
  · obtain hb | hb := Int.even_or_odd b
    -- Odd a ∧ Even b
    · right
      obtain hc | hc := Int.even_or_odd c
      -- Odd a ∧ Even b ∧ Even c
      · right
        dsimp [Even] at *
        obtain ⟨kc, hc'⟩ := hc
        obtain ⟨kb, hb'⟩ := hb
        use kb - kc
        calc
          b - c = 2 * kb - 2 * kc := by rw [hb', hc']
          _ = 2 * (kb - kc) := by ring
      -- Odd a ∧ Even b ∧ Odd c
      · left
        dsimp [Even, Odd] at *
        obtain ⟨ka, ha'⟩ := ha
        obtain ⟨kc, hc'⟩ := hc
        use ka + kc + 1
        calc
          a + c = (2 * ka + 1) + (2 * kc + 1) := by rw [ha', hc']
          _ = 2 * (ka + kc + 1) := by ring
    -- Odd a ∧ Odd b
    · left
      dsimp [Even, Odd] at *
      obtain ⟨ka, ha'⟩ := ha
      obtain ⟨kb, hb'⟩ := hb
      use ka - kb
      calc
        a - b = (2 * ka + 1) - (2 * kb + 1) := by rw [hb', ha']
        _ = 2 * (ka - kb) := by ring
