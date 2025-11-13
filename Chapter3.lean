variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
    Iff.intro
    (fun h : p ∧ q => ⟨h.right,h.left⟩)
    (fun h : q ∧ p => ⟨h.right,h.left⟩)

example : p ∨ q ↔ q ∨ p :=
    Iff.intro
    (fun h : p ∨ q =>
        Or.elim h
        (fun hp : p => Or.inr hp)
        (fun hq : q => Or.inl hq))
    (fun h : q ∨ p =>
        Or.elim h
        (fun hq : q => Or.inr hq)
        (fun hp : p => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
    (fun h : (p ∧ q) ∧ r =>
        have hpq : p ∧ q := h.left
        have hr : r := h.right
        have hp : p := hpq.left
        have hq : q := hpq.right
        show p ∧ (q ∧ r) from ⟨hp,⟨hq,hr⟩⟩)
    (fun h : p ∧ (q ∧ r) =>
        have hp : p := h.left
        have hqr : q ∧ r := h.right
        have hq : q := hqr.left
        have hr : r := hqr.right
        show (p ∧ q) ∧ r from ⟨⟨hp,hq⟩,hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
    (fun h : (p ∨ q) ∨ r =>
        Or.elim h
        (fun hpq : p ∨ q =>
            Or.elim hpq
            (fun hp : p => show p ∨ (q ∨ r) from Or.inl hp)
            (fun hq : q =>
                have hqr : q ∨ r := Or.inl hq
                show p ∨ (q ∨ r) from Or.inr hqr))
        (fun hr : r =>
            have hqr : q ∨ r := Or.inr hr
            show p ∨ (q ∨ r) from Or.inr hqr))
    (fun h : p ∨ (q ∨ r) =>
        Or.elim h
        (fun hp: p =>
            have hpq : p ∨ q := Or.inl hp
            show (p ∨ q) ∨ r from Or.inl hpq)
        (fun hqr : q ∨ r =>
            Or.elim hqr
            (fun hq : q =>
                have hpq : p ∨ q := Or.inr hq
                show (p ∨ q) ∨ r from Or.inl hpq)
            (fun hr : r =>
                show (p ∨ q) ∨ r from Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
    (fun h : p ∧ (q ∨ r) =>
        have hp : p := h.left
        have hqr : q ∨ r := h.right
        Or.elim hqr
        (fun hq : q =>
            have hpq : p ∧ q := ⟨hp,hq⟩
            show (p ∧ q) ∨ (p ∧ r) from Or.inl hpq)
        (fun hr : r =>
            have hpr : p ∧ r := ⟨hp,hr⟩
            show (p ∧ q) ∨ (p ∧ r) from Or.inr hpr))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
        Or.elim h
        (fun hpq : p ∧ q =>
            have hp : p := hpq.left
            have hq : q := hpq.right
            have hqr : q ∨ r := Or.inl hq
            show p ∧ (q ∨ r) from ⟨hp,hqr⟩)
        (fun hpr : p ∧ r =>
            have hp : p := hpr.left
            have hr : r := hpr.right
            have hqr : q ∨ r := Or.inr hr
            show p ∧ (q ∨ r) from ⟨hp,hqr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro
    (fun h : p ∨ (q ∧ r) =>
        Or.elim h
        (fun hp : p =>
            have hpq : p ∨ q := Or.inl hp
            have hpr : p ∨ r := Or.inl hp
            show (p ∨ q) ∧ (p ∨ r) from ⟨hpq,hpr⟩)
        (fun hqr : q ∧ r =>
            have hq : q := hqr.left
            have hr : r := hqr.right
            have hpq : p ∨ q := Or.inr hq
            have hpr : p ∨ r := Or.inr hr
            show (p ∨ q) ∧ (p ∨ r) from ⟨hpq,hpr⟩))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
        have hpq : p ∨ q := h.left
        have hpr : p ∨ r := h.right
        Or.elim hpq
        (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
            Or.elim hpr
            (fun hp₂ : p => show p ∨ (q ∧ r) from Or.inl hp₂)
            (fun hr : r =>
                have hqr : q ∧ r := ⟨hq,hr⟩
                show p ∨ (q ∧ r) from Or.inr hqr)))

example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro
    (fun h : p → (q → r) =>
        fun hpq : p ∧ q =>
        have hp := hpq.left
        have hq := hpq.right
        have hqr := h hp
        show r from hqr hq)
    (fun h : p ∧ q → r =>
        fun hp : p =>
        fun hq : q =>
        have hpq := ⟨hp,hq⟩
        show r from h hpq)

example : (p ∨ q) → r ↔ (p → r) ∧ (q → r) :=
    Iff.intro
    (fun h : (p ∨ q) → r =>
        have hpr : p → r :=
            fun hp : p =>
                have hpq : p ∨ q := Or.inl hp
                show r from h hpq
        have hqr : q → r :=
            fun hq : q =>
                have hpq : p ∨ q := Or.inr hq
                show r from h hpq
        show (p → r) ∧ (q → r) from ⟨hpr,hqr⟩)
    (fun h : (p → r) ∧ (q → r) =>
        have hpr : p → r := h.left
        have hqr : q → r := h.right
        fun hpq : p ∨ q =>
            Or.elim hpq
            (fun hp : p => show r from hpr hp)
            (fun hq : q => show r from hqr hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    Iff.intro
    (fun h : ¬(p ∨ q) =>
        have hnp : ¬p :=
            fun hp : p =>
                have hpq : p ∨ q := Or.inl hp
                show False from h hpq
        have hnq : ¬q :=
            fun hq : q =>
                have hpq : p ∨ q := Or.inr hq
                show False from h hpq
        show ¬p ∧ ¬q from ⟨hnp,hnq⟩)
    (fun h : ¬p ∧ ¬q =>
        have hnp : ¬p := h.left
        have hnq : ¬q := h.right
        fun hpq : p ∨ q =>
            Or.elim hpq
            (fun hp : p => show False from hnp hp)
            (fun hq : q => show False from hnq hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h : ¬p ∨ ¬q =>
        Or.elim h
        (fun hnp : ¬p =>
            fun h₂ : p ∧ q =>
                have hp : p := h₂.left
                show False from hnp hp)
        (fun hnq : ¬q =>
            fun h₂ : p ∧ q =>
                have hq : q := h₂.right
                show False from hnq hq)

example : ¬(p ∧ ¬p) :=
    fun h : p ∧ ¬p =>
        have hp : p := h.left
        have hnp : ¬p := h.right
        show False from hnp hp

example : p ∧ ¬q → ¬(p → q) :=
    fun h : p ∧ ¬q =>
        have hp : p := h.left
        have hnq : ¬q := h.right
        fun h₂ : p → q =>
            have hq : q := h₂ hp
            show False from hnq hq

example : ¬p → (p → q) :=
    fun hnp : ¬p =>
        fun hp : p =>
            absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
    fun h : ¬p ∨ q =>
        fun hp : p =>
            Or.elim h
            (fun hnp : ¬p => absurd hp hnp)
            (fun hq : q => hq)

example : p ∨ False ↔ p :=
    Iff.intro
    (fun h : p ∨ False =>
        Or.elim h
        (fun hp : p => hp)
        (fun h : False => False.elim h))
    (fun hp : p => Or.inl hp)

example : p ∧ False ↔ False :=
    Iff.intro
    (fun h : p ∧ False => show False from h.right)
    (fun h : False => False.elim h)

example : (p → q) → (¬q → ¬p) :=
    fun h : p → q =>
        fun hnq : ¬q =>
            fun hp : p =>
                have hq : q := h hp
                show False from hnq hq

example : ¬(p ↔ ¬p) :=
    fun h : p ↔ ¬p =>
        have h₁ : p → ¬p := Iff.mp h
        have h₂ : ¬p → p := Iff.mpr h
        have y := fun h₃ : p =>
            have x := h₁ h₃
            x h₃
        have z := h₂ y
        show False from y z

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    fun h : p → q ∨ r =>
        Or.elim (em p)
        (fun hp : p =>
            have hqr : q ∨ r := h hp
            Or.elim hqr
            (fun hq : q =>
                have h₁ : p → q := fun _ => hq
                show (p → q) ∨ (p → r) from Or.inl h₁)
            (fun hr : r =>
                have h₁ : p → r := fun _ => hr
                show (p → q) ∨ (p → r) from Or.inr h₁))
        (fun hnp : ¬p =>
            have hpq : p → q := fun hp : p => absurd hp hnp
            show (p → q) ∨ (p → r) from Or.inl hpq)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    fun h : ¬(p ∧ q) =>
        Or.elim (em p)
        (fun hp : p =>
            Or.elim (em q)
            (fun hq : q =>
                have hpq : p ∧ q := ⟨hp,hq⟩
                absurd hpq h)
            (fun hnq : ¬q => show ¬p ∨ ¬q from Or.inr hnq))
        (fun hnp : ¬p => show ¬p ∨ ¬q from Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
    fun h : ¬(p → q) =>
        Or.elim (em p)
        (fun hp : p =>
            -- 构造出 q → False
            have hnq : ¬q :=
                fun hq : q =>
                    have x : p → q := fun _ => hq
                    show False from h x
            show p ∧ ¬q from ⟨hp, hnq⟩)
        (fun hnp : ¬p =>
            -- 构造出 p → q
            have hpq : p → q :=
                fun hp : p => False.elim (hnp hp)
            absurd hpq h)

example : (p → q) → (¬p ∨ q) :=
    fun h : p → q =>
        Or.elim (em p)
        (fun hp : p =>
            have hq : q := h hp
            show ¬p ∨ q from Or.inr hq)
        (fun hnp : ¬p => show ¬p ∨ q from Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
    fun h : ¬q → ¬p =>
        fun hp : p =>
            Or.elim (em q)
            (fun hq : q => hq)
            (fun hnq : ¬q =>
                have hnp : ¬p := h hnq
                absurd hp hnp)

example : p ∨ ¬p :=
    Or.elim (em p)
    (fun hp : p => Or.inl hp)
    (fun hnp : ¬p => Or.inr hnp)

example : ((p → q) → p) → p :=
    fun h : (p → q) → p =>
        Or.elim (em p)
        (fun hp : p => hp)
        (fun hnp : ¬p =>
            have hpq : p → q :=
                fun hp : p => False.elim (hnp hp)
            h hpq)
