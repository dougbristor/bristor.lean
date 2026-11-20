-- SPDX-License-Identifier: MIT  (c) 2026 Doug Bristor, bristorbrot.org — attribution requested, not required
/-!
# B3 — the Bristorian (imordial) product in Lean 4 (core only, no Mathlib)

Doug Bristor's Bristorian algebra (bristorbrot.org), checked in Lean 2026-11-20.
The rule is a choice; what follows from it is not. Lean checks the second part.

The spec is the one-line rule (the i-roll convention):

    e_a · e_b = sgn(b − a) · e_b   (a ≠ b)      e_a · e_a = −1      1 is the identity

so i·j = +j, j·i = −i. B3 = 1 + three imaginary units (i, j, k = e1, e2, e3): four slots,
rank-indexed (slot 0 real, slot a = e_a). Elements are imordials: ranked imaginaries.

What is proved here, and how the chain closes:
  * `table`      — `mul` on the 16 basis pairs IS the one-line rule (checked case by case).
  * `mul_add_*`, `mul_smul_*` — `mul` is bilinear.
  Together these say `mul` is *the* bilinear extension of the rule: no other product fits both.
  The closed form inside `mul` (the form bristorbrot's renderers use) is therefore not trusted, it is
  derived. Everything below is a consequence.

Theorems over any commutative ring `α` (so they hold for ℤ, ℚ, ℝ, floats-as-reals):
  `commutator`, `square_closed`, `jroll_is_reversal`.
Counterexamples over ℤ: `not_assoc`, `not_alternative`, `not_norm_mult`, `not_quaternion`.

Not proved (and not provable here): anything about renders, fields, statistics, or whether a
statement is the right question. Lean checks the statement it is given.
-/

structure B3 (α : Type) where
  r : α
  i : α
  j : α
  k : α
deriving DecidableEq, Repr

namespace B3

section ring
variable {α : Type} [Lean.Grind.CommRing α]

def add (x y : B3 α) : B3 α := ⟨x.r + y.r, x.i + y.i, x.j + y.j, x.k + y.k⟩
def sub (x y : B3 α) : B3 α := ⟨x.r - y.r, x.i - y.i, x.j - y.j, x.k - y.k⟩
def smul (c : α) (x : B3 α) : B3 α := ⟨c * x.r, c * x.i, c * x.j, c * x.k⟩

/-- The canon (i-roll) product. Slot q collects a0·b_q + a_q·b0 + b_q·(Σ_{p<q} a_p − Σ_{p>q} a_p):
the right operand's unit survives, signed by which rank came first. -/
def mul (a b : B3 α) : B3 α :=
  ⟨a.r*b.r - a.i*b.i - a.j*b.j - a.k*b.k,
   a.r*b.i + a.i*b.r + b.i*(0 - (a.j + a.k)),
   a.r*b.j + a.j*b.r + b.j*(a.i - a.k),
   a.r*b.k + a.k*b.r + b.k*(a.i + a.j)⟩

/-- The legacy j-roll (1995 table, i·j = −j, j·i = +i): the same rule with every cross sign flipped. -/
def jmul (a b : B3 α) : B3 α :=
  ⟨a.r*b.r - a.i*b.i - a.j*b.j - a.k*b.k,
   a.r*b.i + a.i*b.r + b.i*(a.j + a.k),
   a.r*b.j + a.j*b.r + b.j*(a.k - a.i),
   a.r*b.k + a.k*b.r + b.k*(0 - (a.i + a.j))⟩

/-- Reverse the rank order of the imaginary units: e1 ↔ e3, e2 fixed. -/
def rev (x : B3 α) : B3 α := ⟨x.r, x.k, x.j, x.i⟩

/-- Squared Euclidean length of the four slots. -/
def norm2 (x : B3 α) : α := x.r*x.r + x.i*x.i + x.j*x.j + x.k*x.k

/-! ## Bilinearity -/

theorem mul_add_left (x y z : B3 α) : mul (add x y) z = add (mul x z) (mul y z) := by
  cases x; cases y; cases z; simp only [mul, add, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem mul_add_right (x y z : B3 α) : mul x (add y z) = add (mul x y) (mul x z) := by
  cases x; cases y; cases z; simp only [mul, add, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem mul_smul_left (c : α) (x y : B3 α) : mul (smul c x) y = smul c (mul x y) := by
  cases x; cases y; simp only [mul, smul, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem mul_smul_right (c : α) (x y : B3 α) : mul x (smul c y) = smul c (mul x y) := by
  cases x; cases y; simp only [mul, smul, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ## Structure theorems (any commutative ring) -/

/-- The commutator: each pair p<q contributes (x_p y_q − x_q y_p)·(e_p + e_q). Real part 0.
The commutator signature [e_p, e_q] = +(e_p + e_q) (i-roll) is the basis case. -/
theorem commutator (x y : B3 α) :
    sub (mul x y) (mul y x) =
      let w12 := x.i*y.j - x.j*y.i
      let w13 := x.i*y.k - x.k*y.i
      let w23 := x.j*y.k - x.k*y.j
      ⟨0, w12 + w13, w12 + w23, w13 + w23⟩ := by
  cases x; cases y; simp only [mul, sub, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Closed form of the square (the form the renderers use):
real = x² − Σ y_a²,  e_b = y_b·(2x + Σ_{a<b} y_a − Σ_{a>b} y_a). -/
theorem square_closed (z : B3 α) :
    mul z z = ⟨z.r*z.r - z.i*z.i - z.j*z.j - z.k*z.k,
               z.i*(z.r + z.r - z.j - z.k),
               z.j*(z.r + z.r + z.i - z.k),
               z.k*(z.r + z.r + z.i + z.j)⟩ := by
  cases z; simp only [mul, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- The two rolls are one algebra relabelled, not a correction: the j-roll product is the
i-roll product with the rank order reversed (the two conventions are one algebra, relabelled). -/
theorem jroll_is_reversal (x y : B3 α) : jmul x y = rev (mul (rev x) (rev y)) := by
  cases x; cases y; simp only [jmul, mul, rev, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

end ring

/-! ## The table and the counterexamples (over ℤ, checked by evaluation) -/

/-- Basis element e_a (a = 0 is the real unit 1). -/
def e : Fin 4 → B3 Int
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩

/-- The one-line rule, written as the rule and nothing else. -/
def rule (a b : Fin 4) : B3 Int :=
  if a = 0 then e b
  else if b = 0 then e a
  else if a = b then smul (-1) (e 0)
  else if a < b then e b
  else smul (-1) (e b)

/-- `mul` on every basis pair is the rule. With bilinearity, this pins `mul` down completely. -/
theorem table : ∀ a b : Fin 4, mul (e a) (e b) = rule a b := by decide

/-- Commutator signature, i-roll: [e_p, e_q] = +(e_p + e_q) for 0 < p < q. -/
theorem commutator_signature :
    ∀ p q : Fin 4, 0 < p → p < q → sub (mul (e p) (e q)) (mul (e q) (e p)) = add (e p) (e q) := by
  decide

/-- Non-associative: (i·j)·i = −i but i·(j·i) = +1. -/
theorem not_assoc : mul (mul (e 1) (e 2)) (e 1) = ⟨0, -1, 0, 0⟩ ∧
    mul (e 1) (mul (e 2) (e 1)) = ⟨1, 0, 0, 0⟩ := by decide

/-- Non-alternative: the associator (i, i, j) = (i·i)·j − i·(i·j) = −2j ≠ 0. -/
theorem not_alternative :
    sub (mul (mul (e 1) (e 1)) (e 2)) (mul (e 1) (mul (e 1) (e 2))) = ⟨0, 0, -2, 0⟩ := by decide

/-- Not norm-multiplicative: |(1+i)(1+j)|² = 6 but |1+i|²·|1+j|² = 4. -/
theorem not_norm_mult : norm2 (mul (⟨1, 1, 0, 0⟩ : B3 Int) ⟨1, 0, 1, 0⟩) = 6 ∧
    norm2 (⟨1, 1, 0, 0⟩ : B3 Int) * norm2 (⟨1, 0, 1, 0⟩ : B3 Int) = 4 := by decide

/-- Not the quaternions: i·j = +j here, and k (Hamilton's i·j) does not appear. -/
theorem not_quaternion : mul (e 1) (e 2) = e 2 ∧ mul (e 1) (e 2) ≠ e 3 := by decide

end B3
