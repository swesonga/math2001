/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain ha | hb := h -- <;>
    constructor <;> obtain ⟨h3, h4⟩ := ha
    · apply h3
    · left
      apply h4
    constructor <;> obtain ⟨h3, h4⟩ := hb
    · apply h3
    right
    apply h4


#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hp, hq⟩ := h
  left
  apply hp

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  apply h1
  apply h3
  apply h2
  apply h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨hp, hnotp⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro h
  rw [h1] at h
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain hp | hq := h1
  apply hp
  --rw [hq] at h2 -- only works for iff
  apply h2
  apply hq

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  · intro h2
    obtain ⟨hp, hr⟩ := h2
    rw [h] at hp
    constructor
    apply hp
    apply hr
  · intro h2
    obtain ⟨hq, hr⟩ := h2
    constructor
    rw [h] -- accidental discovery that this is right?
    apply hq
    apply hr

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro h
    obtain ⟨hp, hp2⟩ := h
    apply hp
  · intro h
    constructor <;> apply h


example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor <;> intro h <;> obtain hl | hr := h
  right
  apply hl
  left
  apply hr
  right
  apply hl
  left
  apply hr

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor <;> intro h
  · constructor
    · intro hp
      have : P ∨ Q := by
        left
        apply hp
      contradiction
    · intro hq
      have : P ∨ Q := by
        right
        apply hq
      contradiction
  obtain ⟨hnp, hnq⟩ := h
  intro h2
  obtain hp | hq := h2
  contradiction
  contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1
  apply h2

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor <;> intro h2 <;> obtain ⟨x, hx⟩ := h2
  use x
  rw [h] at hx
  apply hx
  use x
  rw [h]
  apply hx

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor <;> intro h2 <;> obtain ⟨x, y, h3⟩ := h2
  use y, x
  apply h3
  use y, x
  apply h3

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor <;> intro h
  intro y x
  apply h
  intro x y
  apply h

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor <;> intro h
  · obtain ⟨h1, hq⟩ := h
    obtain ⟨x, h2⟩ := h1
    use x
    constructor
    apply h2
    apply hq
  obtain ⟨x, hpx, hq⟩ := h
  constructor
  · use x
    apply hpx
  apply hq
