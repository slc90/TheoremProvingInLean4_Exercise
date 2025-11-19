section
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  . intro h
    constructor
    . exact h.right
    . exact h.left
  . intro h
    exact And.intro h.right h.left

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  . intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  case mp =>
    intro h
    constructor
    case left => exact h.left.left
    case right =>
      have hq := h.left.right
      apply And.intro
      exact hq
      exact h.right
  case mpr =>
    intro h
    constructor
    . constructor
      . exact h.left
      . exact h.right.left
    . exact h.right.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp =>
        apply Or.inl
        exact hp
      | inr hq =>
        apply Or.inr
        apply Or.inl
        exact hq
    | inr hr =>
      apply Or.inr
      apply Or.inr
      exact hr
  . intro h
    cases h with
    | inl hp =>
      apply Or.inl
      apply Or.inl
      exact hp
    | inr hqr =>
      cases hqr with
      | inl hq =>
        apply Or.inl
        apply Or.inr
        exact hq
      | inr hr =>
        apply Or.inr
        exact hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro h
    have hp := h.left
    have hqr := h.right
    cases hqr with
    | inl hq =>
      apply Or.inl
      apply And.intro
      . exact hp
      . exact hq
    | inr hr =>
      apply Or.inr
      apply And.intro
      . exact hp
      . exact hr
  . intro h
    cases h with
    | inl hpq=>
      have hp := hpq.left
      have hq := hpq.right
      apply And.intro
      . exact hp
      . apply Or.inl
        exact hq
    | inr hpr =>
      have hp := hpr.left
      have hr := hpr.right
      apply And.intro
      . exact hp
      . apply Or.inr
        exact hr

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro h
    cases h with
    | inl hp =>
      constructor
      . apply Or.inl
        exact hp
      . apply Or.inl
        exact hp
    | inr hqr =>
      constructor
      . apply Or.inr
        exact hqr.left
      . apply Or.inr
        exact hqr.right
  . intro h
    have hpq := h.left
    have hpr := h.right
    cases hpq with
    | inl hp =>
      apply Or.inl
      exact hp
    | inr hq =>
      cases hpr with
      | inl hp =>
        apply Or.inl
        exact hp
      | inr hr =>
        have hqr := And.intro hq hr
        apply Or.inr
        exact hqr

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro hpqr hpr
    have hp := hpr.left
    have hr := hpr.right
    exact hpqr hp hr
  . intro hpqr hp hq
    apply hpqr
    exact ⟨hp,hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h
    constructor
    . intro hp
      apply h
      apply Or.inl hp
    . intro hq
      apply h
      exact Or.inr hq
  . intro h hpq
    have hpr := h.left
    have hqr := h.right
    cases hpq
    . apply hpr
      assumption
    . apply hqr
      assumption

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h
    constructor
    . intro hp
      apply h
      exact Or.inl hp
    . intro hq
      apply h
      exact Or.inr hq
  . intro h hpq
    have hnp := h.left
    have hnq := h.right
    cases hpq
    . apply hnp
      assumption
    . apply hnq
      assumption

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h ⟨hp,hq⟩
  cases h with
  | inl hnp => apply hnp hp
  | inr hnq => apply hnq hq

example : ¬(p ∧ ¬p) := by
  intro h
  have hp := h.left
  have hnp := h.right
  apply hnp hp

example : p ∧ ¬q → ¬(p → q) := by
  intro h hpq
  have hp := h.left
  have hnq := h.right
  apply hnq
  apply hpq
  exact hp

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h with
  | inl hnp => contradiction
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  constructor
  . intro h
    cases h
    . assumption
    . contradiction
  . intro hp
    apply Or.inl
    exact hp

example : p ∧ False ↔ False := by
  constructor
  . intro h
    exact h.right
  . intro
    contradiction

example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
  have hq := h hp
  contradiction
end

section
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hpq
  by_cases h : p
  . have hqr := hpq h
    cases hqr with
    | inl hq =>
      apply Or.inl
      intro
      exact hq
    | inr hr =>
      apply Or.inr
      intro
      exact hr
  . left
    intro hp
    have : False := h hp
    contradiction

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_cases hp :p
  . by_cases hq : q
    . have hpq := And.intro hp hq
      have : False := h hpq
      contradiction
    . apply Or.inr
      assumption
  . apply Or.inl
    assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  by_cases hp : p
  . by_cases hq : q
    . have hpq := fun _ : p => hq
      have : False := h hpq
      contradiction
    . apply And.intro
      . exact hp
      . exact hq
  . have hpq : p → q := fun h1 : p => by
      have :False := hp h1
      contradiction
    have : False := h hpq
    contradiction

example : (p → q) → (¬p ∨ q) := by
  intro hpq
  by_cases hp : p
  . apply Or.inr
    apply hpq
    exact hp
  . apply Or.inl
    assumption

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  by_cases hq : q
  . assumption
  . have hnp := h hq
    have : False := hnp hp
    contradiction

example : p ∨ ¬p := by
  by_cases hp : p
  . apply Or.inl
    assumption
  . apply Or.inr
    assumption

example : (((p → q) → p) → p) := by
  intro h
  by_cases hp : p
  . assumption
  . have hpq : p → q :=
      fun h1 : p => by
        have : False := hp h1
        contradiction
    apply h
    exact hpq
end

section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    . intro x
      specialize h x
      exact h.left
    . intro x
      specialize h x
      exact h.right
  . intro h
    have h1 := h.left
    have h2 := h.right
    intro x
    constructor
    . apply h1 x
    . apply h2 x

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2 x
  specialize h2 x
  specialize h1 x
  apply h1
  assumption

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl h1 =>
      apply Or.inl
      specialize h1 x
      assumption
  | inr h2 =>
      right
      specialize h2 x
      assumption
end

section
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro x
  constructor
  . intro h
    apply h
    exact x
  . intro h
    intro x
    assumption

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . by_cases hr : r
    . intro
      right
      exact hr
    . intro h
      left
      intro x
      specialize h x
      cases h with
      | inl => assumption
      | inr => contradiction
  . intro h x
    cases h with
    | inl h1 =>
      left
      specialize h1 x
      assumption
    | inr =>
      right
      assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro h hr x
    specialize h x
    apply h
    assumption
  . intro h x hr
    have h1 := h hr
    specialize h1 x
    assumption
end

section
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  specialize h barber
  have ⟨h1,h2⟩ := h
  have h4 :=
    fun y : shaves barber barber =>
      have h5 := h1 y
      h5 y
  have x := h2 h4
  have : False := h4 x
  contradiction
end

section
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro h
  cases h with
  | intro x hr => exact hr

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exists a

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  . intro h
    cases h with
    | intro x px =>
      constructor
      . exists x
        exact px.left
      . exact px.right
  . intro h
    cases h with
    | intro h1 hr =>
      cases h1 with
      | intro x px =>
        exists x

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro h
    cases h with
    | intro x hpq =>
      cases hpq with
      | inl hp =>
        left
        exists x
      | inr hq =>
        right
        exists x
  . intro h
    cases h with
    | inl h1 =>
      cases h1 with
      | intro x px =>
        exists x
        left
        assumption
    | inr h2 =>
      cases h2 with
      | intro x hq =>
        exists x
        right
        exact hq

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  . intro h h1
    cases h1 with
    | intro x npx =>
      have px := h x
      contradiction
  . intro h x
    by_cases h1 : p x
    . exact h1
    . have h2 : ∃ x, ¬p x := ⟨x, fun h : p x => h1 h⟩
      have : False := h h2
      contradiction

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  . intro h1 h2
    cases h1 with
    | intro x px =>
      have npx := h2 x
      contradiction
  . intro h
    false_or_by_contra
    apply h
    intro x px
    have : ∃ x, p x := ⟨x,px⟩
    contradiction

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  . intro h x px
    have : ∃ x, p x := ⟨x, px⟩
    contradiction
  . intro h1 h2
    cases h2 with
    | intro x px =>
      have npx := h1 x
      contradiction

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  . intro h
    false_or_by_contra
    apply h
    intro x
    by_cases h2 : p x
    . assumption
    . have : ∃ x, ¬p x := ⟨x,h2⟩
      contradiction
  . intro h1 h2
    cases h1 with
    | intro x npx =>
      have px := h2 x
      contradiction

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  . intro h1 h2
    cases h2 with
    | intro x px =>
      have h3 := h1 x
      apply h3
      assumption
  . intro h x px
    have h1 : ∃ x, p x := ⟨x,px⟩
    apply h
    exact h1

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  . intro h1 h2
    cases h1 with
    | intro x pxr =>
      have px := h2 x
      apply pxr
      assumption
  . intro h
    by_cases H : ∀ x, p x
    · have hr : r := h H
      exists a
      intro
      exact hr
    . sorry

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  . intro h hr
    cases h with
    | intro x rpx =>
      have px := rpx hr
      exists x
  . intro h
    by_cases hr : r
    . have h2 := h hr
      have ⟨x,px⟩ := h2
      exists x
      intro
      assumption
    . exists a
      intro h2
      have : False := hr h2
      contradiction
end
