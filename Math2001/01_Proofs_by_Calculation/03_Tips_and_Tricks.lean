/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/

/-
I attempted these exercises before reading the tips and tricks in the text.
I have documented the places I got stuck to highlight what I didn't know before reading the text.
-/

-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

/-
I struggled initially because I didn't put x on the left side by itself
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    (x + 4) - 4 = 2 - 4 := by rw [h1]
    _ = -2 := by ring
    _ = x := by ring
    -- x + (4 - 4) = 2 - 4 := by ring
    x = -2 := by ring
-/

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = 4 + 5 * ((b + 2) - 2) := by ring
    _ = 4 + 5 * (3 - 2) := by rw [h2]
    _ = 9 := by ring

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = ((3*w + 1) - 1)/3 := by ring
    _ = (4 - 1)/3 := by rw [h1]
    _ = 1 := by ring

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    -- x = ((2*x + 3) - 3)/2 := by ring -- division doesn't work like this in the ring of integers!
    -- looking at 1.3.4 now, shouldn't it be something like := by field?
    x = ((2 * x + 3) - 3) - x := by ring
    _ = x - 3 - x := by rw [h1]
    _ = -3 := by ring

-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x = (2 * x - y) + y - x := by ring
    _ = 4 + y - x := by rw [h1]
    _ = 4 + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h2]

/-
-- Example 1.3.7 -- Initial attempt
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = (u + 2 * v) - 2 * v := by ring
    _ = 4 - 2 * v := by rw [h1]
    _ = 4 - 2 * v + u - u := by ring
--    _ = 4 + (- 2 * v + u) - u := by ring
    _ = 4 + (u - 2 * v) - u := by ring
    _ = 4 + 6 - u := by rw [h2]
    _ = 10 - u := by ring

-- Example 1.3.7 -- second attempt
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = u + 2 * v - 2 * v + (u - 2 * v) + 2 * v - u:= by ring
    _ = 4 - 2 * v + 6 + 2 * v - u := by rw [h1, h2]
    _ = 10 - u := by ring
-/

-- Example 1.3.7 (after reading this example in the text)
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = (u + 2 * v + u - 2 * v)/2 := by ring
    _ = (u + 2 * v + (u - 2 * v))/2 := by ring
    _ = (4 + 6)/2 := by rw [h1, h2]
    _ = 5 := by ring

/-
-- Example 1.3.8 -- attempt 1
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = 3*(x + y) - 2*x - 3*y := by ring
    _ = 3*4 - 2*x - 3*y := by rw [h1]
    _ = 12 - 2 * x - 3 * y := by ring
    _ = 12 - 2 * x - 3 * y - x + x := by ring
    _ = 12 - 3 * x - 3 * y - x := by ring

-- Example 1.3.8 -- attempt 2
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = 3*(x + y) - 2*x - 3*y := by ring
    _ = 3*4 - 2*x - 3*y := by rw [h1]
    _ = 12 - 2*x - 3*y + 7 * x - 7 * x := by ring
    _ = 12 + (5 * x - 3*y) - 7 * x := by ring
    _ = 12 + 4 - 7 * x := by rw [h2]
    _ = 16 - 7 * x := by ring
-/

-- Example 1.3.8 -- Needed to read the text to see how to proceed on this one
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = (3*(x + y) + (5 * x - 3 * y))/8 := by ring
    _ = (3*4 + 4)/8 := by rw [h1, h2]
    _ = 2 := by ring

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = (a - 3 + 3)^2 - (a - 3 + 3) + 3 := by ring
    _ = (2 * b + 3)^2 - (2 * b + 3) + 3 := by rw [h1]
    _ = (4 * b^2 + 12 * b + 9) - (2 * b + 3) + 3 := by ring
    _ = 4 * b^2 + 10 * b + 9 := by ring

/-
-- Example 1.3.10 -- initial attempt
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 - 3 + 3 := by ring
    _ = z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 - 2 + 2 := by ring
    _ = z ^ 4 - z ^ 3 - (z ^ 2 - 2) + 2 * z + 1 - 2 := by ring
    -- _ = z ^ 4 - z ^ 3 - (z ^ 2 + 2) + 2 * z + 1 + 2 := by ring
    _ = z ^ 4 - z ^ 3 - (0) + 2 * z + 1 - 2 := by rw [h1]
-/

-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = (z ^ 2 - z + 1) * (z ^ 2 - 2) + 3 := by ring
    _ = (z ^ 2 - z + 1) * 0 + 3 := by rw [h1]
    _ = 3 := by ring

/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  sorry

example {a b : ℤ} (h : a - b = 0) : a = b :=
  sorry

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  sorry

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  sorry

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  sorry

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  sorry

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  sorry

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  sorry

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  sorry

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  sorry

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  sorry

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  sorry

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  sorry

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  sorry

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  sorry

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  sorry
