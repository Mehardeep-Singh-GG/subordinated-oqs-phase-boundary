/-
  Exact Analytic Phase Boundary Between Complete Monotonicity,
  CP-Divisibility, and Information Backflow in Time-Subordinated Open Quantum Dynamics.

  Pure Lean 4.16.0 formalization (NO Mathlib, zero sorry, zero admit, zero custom axioms).
  Verified with `#print axioms` on every main theorem.
-/

namespace DiamondProofs.Paper2

/-! ## Part I: Algebraic Field Interfaces and Exact Rational Field `Q` -/

class FieldOps (α : Type) where
  zero : α
  one : α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α

instance {α : Type} [FieldOps α] : OfNat α 0 := ⟨FieldOps.zero⟩
instance {α : Type} [FieldOps α] : OfNat α 1 := ⟨FieldOps.one⟩
instance {α : Type} [FieldOps α] : HAdd α α α := ⟨FieldOps.add⟩
instance {α : Type} [FieldOps α] : Neg α := ⟨FieldOps.neg⟩
instance {α : Type} [FieldOps α] : HMul α α α := ⟨FieldOps.mul⟩
instance {α : Type} [FieldOps α] : HSub α α α := ⟨fun a b => a + (-b)⟩
instance {α : Type} [FieldOps α] : HDiv α α α := ⟨fun a b => a * FieldOps.inv b⟩

class CommField (α : Type) extends FieldOps α where
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, (0 : α) + a = a
  add_neg_cancel : ∀ a : α, a + (-a) = (0 : α)
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, (1 : α) * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  mul_inv_cancel : ∀ a : α, a ≠ (0 : α) → a * FieldOps.inv a = (1 : α)
  inv_zero : FieldOps.inv (0 : α) = (0 : α)
  zero_ne_one : (0 : α) ≠ (1 : α)

class OrderedField (α : Type) extends CommField α where
  le : α → α → Prop
  lt : α → α → Prop
  le_refl : ∀ a : α, le a a
  le_trans : ∀ {a b c : α}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : α}, le a b → le b a → a = b
  le_total : ∀ a b : α, le a b ∨ le b a
  lt_iff_le_not_le : ∀ a b : α, lt a b ↔ le a b ∧ ¬ le b a
  add_le_add_left : ∀ {a b : α} (c : α), le a b → le (c + a) (c + b)
  mul_nonneg : ∀ {a b : α}, le (0 : α) a → le (0 : α) b → le (0 : α) (a * b)
  mul_pos : ∀ {a b : α}, lt (0 : α) a → lt (0 : α) b → lt (0 : α) (a * b)

instance {α : Type} [OrderedField α] : LE α := ⟨OrderedField.le⟩
instance {α : Type} [OrderedField α] : LT α := ⟨OrderedField.lt⟩

section FieldLemmas

variable {F : Type} [CommField F]

def ofNatF : Nat → F
  | 0 => 0
  | n + 1 => ofNatF n + 1

theorem add_zero (a : F) : a + 0 = a := by
  rw [CommField.add_comm, CommField.zero_add]

theorem neg_add_cancel (a : F) : -a + a = 0 := by
  rw [CommField.add_comm, CommField.add_neg_cancel]

theorem mul_one (a : F) : a * 1 = a := by
  rw [CommField.mul_comm, CommField.one_mul]

theorem right_distrib (a b c : F) : (a + b) * c = a * c + b * c := by
  rw [CommField.mul_comm, CommField.left_distrib, CommField.mul_comm c a, CommField.mul_comm c b]

theorem add_right_comm (a b c : F) : a + b + c = a + c + b := by
  rw [CommField.add_assoc, CommField.add_comm b c, ← CommField.add_assoc]

theorem add_left_comm (a b c : F) : a + (b + c) = b + (a + c) := by
  rw [← CommField.add_assoc, CommField.add_comm a b, CommField.add_assoc]

theorem mul_right_comm (a b c : F) : a * b * c = a * c * b := by
  rw [CommField.mul_assoc, CommField.mul_comm b c, ← CommField.mul_assoc]

theorem mul_left_comm (a b c : F) : a * (b * c) = b * (a * c) := by
  rw [← CommField.mul_assoc, CommField.mul_comm a b, CommField.mul_assoc]

theorem zero_mul (a : F) : 0 * a = 0 := by
  have h : (0 : F) * a + 0 * a = 0 * a + 0 := by
    calc (0 : F) * a + 0 * a = ((0 : F) + 0) * a := by rw [← right_distrib]
      _ = 0 * a := by rw [CommField.zero_add]
      _ = 0 * a + 0 := by rw [add_zero]
  have h2 := congrArg (fun x => -((0 : F) * a) + x) h
  dsimp at h2
  rw [← CommField.add_assoc, neg_add_cancel, CommField.zero_add,
      ← CommField.add_assoc, neg_add_cancel, CommField.zero_add] at h2
  exact h2

theorem mul_zero (a : F) : a * 0 = 0 := by
  rw [CommField.mul_comm, zero_mul]

theorem neg_eq_neg_one_mul (a : F) : -a = (-1) * a := by
  have h : a + (-1 : F) * a = 0 := by
    calc a + (-1 : F) * a = (1 : F) * a + (-1 : F) * a := by rw [CommField.one_mul]
      _ = ((1 : F) + (-1 : F)) * a := by rw [← right_distrib]
      _ = 0 * a := by rw [CommField.add_neg_cancel]
      _ = 0 := zero_mul a
  calc -a = -a + (a + (-1 : F) * a) := by rw [h, add_zero]
    _ = (-a + a) + (-1 : F) * a := by rw [CommField.add_assoc]
    _ = (-1 : F) * a := by rw [neg_add_cancel, CommField.zero_add]

theorem neg_mul (a b : F) : (-a) * b = -(a * b) := by
  rw [neg_eq_neg_one_mul a, CommField.mul_assoc, ← neg_eq_neg_one_mul (a * b)]

theorem mul_neg (a b : F) : a * (-b) = -(a * b) := by
  rw [CommField.mul_comm, neg_mul, CommField.mul_comm]

theorem neg_neg (a : F) : -(-a) = a := by
  calc -(-a) = -(-a) + (-a + a) := by rw [neg_add_cancel, add_zero]
    _ = (-(-a) + -a) + a := by rw [CommField.add_assoc]
    _ = a := by rw [neg_add_cancel, CommField.zero_add]

theorem neg_add (a b : F) : -(a + b) = -a + -b := by
  rw [neg_eq_neg_one_mul (a + b), CommField.left_distrib, ← neg_eq_neg_one_mul a, ← neg_eq_neg_one_mul b]

theorem neg_zero : -(0 : F) = 0 := by
  calc -(0 : F) = 0 + -(0 : F) := by rw [CommField.zero_add]
    _ = 0 := CommField.add_neg_cancel 0

theorem sub_def (a b : F) : a - b = a + -b := rfl

theorem sub_self (a : F) : a - a = 0 := CommField.add_neg_cancel a

theorem sub_zero (a : F) : a - 0 = a := by
  change a + -(0 : F) = a
  rw [neg_zero, add_zero]

theorem zero_sub (a : F) : 0 - a = -a := by
  change (0 : F) + -a = -a
  exact CommField.zero_add (-a)

theorem add_sub_cancel (a b : F) : (a + b) - b = a := by
  change (a + b) + (-b) = a
  rw [CommField.add_assoc, CommField.add_neg_cancel, add_zero]

theorem sub_add_cancel (a b : F) : (a - b) + b = a := by
  change (a + (-b)) + b = a
  rw [CommField.add_assoc, neg_add_cancel, add_zero]

theorem mul_sub (a b c : F) : a * (b - c) = a * b - a * c := by
  change a * (b + (-c)) = a * b + -(a * c)
  rw [CommField.left_distrib, mul_neg]

theorem sub_mul (a b c : F) : (a - b) * c = a * c - b * c := by
  change (a + (-b)) * c = a * c + -(b * c)
  rw [right_distrib, neg_mul]

theorem neg_mul_neg (a b : F) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem inv_mul_cancel {a : F} (ha : a ≠ 0) : FieldOps.inv a * a = 1 := by
  rw [CommField.mul_comm, CommField.mul_inv_cancel a ha]

theorem div_mul_cancel (a : F) {b : F} (hb : b ≠ 0) : (a / b) * b = a := by
  change (a * FieldOps.inv b) * b = a
  rw [CommField.mul_assoc, inv_mul_cancel hb, mul_one]

theorem add_div (a b c : F) : (a + b) / c = a / c + b / c := by
  change (a + b) * FieldOps.inv c = a * FieldOps.inv c + b * FieldOps.inv c
  exact right_distrib a b (FieldOps.inv c)

theorem sub_div (a b c : F) : (a - b) / c = a / c - b / c := by
  change (a - b) * FieldOps.inv c = a * FieldOps.inv c - b * FieldOps.inv c
  exact sub_mul a b (FieldOps.inv c)

theorem mul_div_assoc (a b c : F) : (a * b) / c = a * (b / c) := by
  change (a * b) * FieldOps.inv c = a * (b * FieldOps.inv c)
  exact CommField.mul_assoc a b (FieldOps.inv c)

end FieldLemmas

section OrderedFieldLemmas

variable {F : Type} [OrderedField F]

theorem lt_irrefl (a : F) : ¬ (a < a) := by
  intro h
  have h1 := (OrderedField.lt_iff_le_not_le a a).mp h
  exact h1.2 h1.1

theorem le_of_lt {a b : F} (h : a < b) : a ≤ b :=
  ((OrderedField.lt_iff_le_not_le a b).mp h).1

theorem not_le_of_lt {a b : F} (h : a < b) : ¬ (b ≤ a) :=
  ((OrderedField.lt_iff_le_not_le a b).mp h).2

theorem lt_of_le_not_le {a b : F} (h1 : a ≤ b) (h2 : ¬ (b ≤ a)) : a < b :=
  (OrderedField.lt_iff_le_not_le a b).mpr ⟨h1, h2⟩

theorem ne_of_lt {a b : F} (h : a < b) : a ≠ b := by
  intro heq
  subst heq
  exact lt_irrefl a h

theorem ne_of_gt {a b : F} (h : b < a) : a ≠ b :=
  (ne_of_lt h).symm

theorem lt_of_lt_of_le {a b c : F} (hab : a < b) (hbc : b ≤ c) : a < c := by
  apply lt_of_le_not_le (OrderedField.le_trans (le_of_lt hab) hbc)
  intro hca
  exact not_le_of_lt hab (OrderedField.le_trans hbc hca)

theorem lt_of_le_of_lt {a b c : F} (hab : a ≤ b) (hbc : b < c) : a < c := by
  apply lt_of_le_not_le (OrderedField.le_trans hab (le_of_lt hbc))
  intro hca
  exact not_le_of_lt hbc (OrderedField.le_trans hca hab)

theorem lt_trans {a b c : F} (hab : a < b) (hbc : b < c) : a < c :=
  lt_of_lt_of_le hab (le_of_lt hbc)

theorem add_le_add_right {a b : F} (c : F) (h : a ≤ b) : a + c ≤ b + c := by
  rw [CommField.add_comm a c, CommField.add_comm b c]
  exact OrderedField.add_le_add_left c h

theorem add_le_add {a b c d : F} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  OrderedField.le_trans (add_le_add_right c h1) (OrderedField.add_le_add_left b h2)

theorem add_lt_add_left {a b : F} (c : F) (h : a < b) : c + a < c + b := by
  apply lt_of_le_not_le (OrderedField.add_le_add_left c (le_of_lt h))
  intro hle
  have h2 := OrderedField.add_le_add_left (-c) hle
  rw [← CommField.add_assoc, ← CommField.add_assoc, neg_add_cancel,
      CommField.zero_add, CommField.zero_add] at h2
  exact not_le_of_lt h h2

theorem add_lt_add_right {a b : F} (c : F) (h : a < b) : a + c < b + c := by
  rw [CommField.add_comm a c, CommField.add_comm b c]
  exact add_lt_add_left c h

theorem add_lt_add {a b c d : F} (h1 : a < b) (h2 : c < d) : a + c < b + d :=
  lt_trans (add_lt_add_right c h1) (add_lt_add_left b h2)

theorem add_lt_add_of_le_of_lt {a b c d : F} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right c h1) (add_lt_add_left b h2)

theorem add_lt_add_of_lt_of_le {a b c d : F} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right c h1) (OrderedField.add_le_add_left b h2)

theorem add_pos {a b : F} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  have h := add_lt_add ha hb
  rw [CommField.zero_add] at h
  exact h

theorem add_pos_of_pos_of_nonneg {a b : F} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by
  have h := add_lt_add_of_lt_of_le ha hb
  rw [CommField.zero_add] at h
  exact h

theorem add_pos_of_nonneg_of_pos {a b : F} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  have h := add_lt_add_of_le_of_lt ha hb
  rw [CommField.zero_add] at h
  exact h

theorem add_nonneg {a b : F} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have h := add_le_add ha hb
  rw [CommField.zero_add] at h
  exact h

theorem sub_nonneg_of_le {a b : F} (h : a ≤ b) : 0 ≤ b - a := by
  have h1 := add_le_add_right (-a) h
  rw [CommField.add_neg_cancel] at h1
  exact h1

theorem le_of_sub_nonneg {a b : F} (h : 0 ≤ b - a) : a ≤ b := by
  have h1 := add_le_add_right a h
  rw [CommField.zero_add, sub_add_cancel] at h1
  exact h1

theorem sub_pos_of_lt {a b : F} (h : a < b) : 0 < b - a := by
  have h1 := add_lt_add_right (-a) h
  rw [CommField.add_neg_cancel] at h1
  exact h1

theorem lt_of_sub_pos {a b : F} (h : 0 < b - a) : a < b := by
  have h1 := add_lt_add_right a h
  rw [CommField.zero_add, sub_add_cancel] at h1
  exact h1

theorem neg_nonneg_of_nonpos {a : F} (h : a ≤ 0) : 0 ≤ -a := by
  have h1 := sub_nonneg_of_le h
  rw [zero_sub] at h1
  exact h1

theorem neg_pos_of_neg {a : F} (h : a < 0) : 0 < -a := by
  have h1 := sub_pos_of_lt h
  rw [zero_sub] at h1
  exact h1

theorem neg_lt_zero_of_pos {a : F} (h : 0 < a) : -a < 0 := by
  have h1 := add_lt_add_right (-a) h
  rw [CommField.zero_add, CommField.add_neg_cancel] at h1
  exact h1

theorem neg_le_zero_of_nonneg {a : F} (h : 0 ≤ a) : -a ≤ 0 := by
  have h1 := add_le_add_right (-a) h
  rw [CommField.zero_add, CommField.add_neg_cancel] at h1
  exact h1

theorem nonpos_of_neg_nonneg {a : F} (h : 0 ≤ -a) : a ≤ 0 := by
  have h1 := add_le_add_right a h
  rw [CommField.zero_add, neg_add_cancel] at h1
  exact h1

theorem neg_of_neg_pos {a : F} (h : 0 < -a) : a < 0 := by
  have h1 := add_lt_add_right a h
  rw [CommField.zero_add, neg_add_cancel] at h1
  exact h1

theorem mul_le_mul_of_nonneg_left {a b c : F} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  apply le_of_sub_nonneg
  rw [← mul_sub]
  exact OrderedField.mul_nonneg hc (sub_nonneg_of_le h)

theorem mul_le_mul_of_nonneg_right {a b c : F} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [CommField.mul_comm a c, CommField.mul_comm b c]
  exact mul_le_mul_of_nonneg_left h hc

theorem mul_lt_mul_of_pos_left {a b c : F} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  apply lt_of_sub_pos
  rw [← mul_sub]
  exact OrderedField.mul_pos hc (sub_pos_of_lt h)

theorem mul_lt_mul_of_pos_right {a b c : F} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  rw [CommField.mul_comm a c, CommField.mul_comm b c]
  exact mul_lt_mul_of_pos_left h hc

theorem mul_nonpos_of_nonpos_of_nonneg {a b : F} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  have h : 0 ≤ (-a) * b := OrderedField.mul_nonneg (neg_nonneg_of_nonpos ha) hb
  rw [neg_mul] at h
  exact nonpos_of_neg_nonneg h

theorem mul_neg_of_neg_of_pos {a b : F} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : 0 < (-a) * b := OrderedField.mul_pos (neg_pos_of_neg ha) hb
  rw [neg_mul] at h
  exact neg_of_neg_pos h

theorem mul_nonneg_of_nonpos_of_nonpos {a b : F} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have h := OrderedField.mul_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)
  rw [neg_mul_neg] at h
  exact h

theorem mul_pos_of_neg_of_neg {a b : F} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have h := OrderedField.mul_pos (neg_pos_of_neg ha) (neg_pos_of_neg hb)
  rw [neg_mul_neg] at h
  exact h

theorem sq_nonneg (a : F) : 0 ≤ a * a := by
  rcases OrderedField.le_total 0 a with h | h
  · exact OrderedField.mul_nonneg h h
  · exact mul_nonneg_of_nonpos_of_nonpos h h

theorem sq_pos_of_ne_zero {a : F} (ha : a ≠ 0) : 0 < a * a := by
  rcases OrderedField.le_total 0 a with h | h
  · have hpos : 0 < a := lt_of_le_not_le h (fun hle => ha (OrderedField.le_antisymm hle h))
    exact OrderedField.mul_pos hpos hpos
  · have hneg : a < 0 := lt_of_le_not_le h (fun hle => ha (OrderedField.le_antisymm h hle))
    have hpos : 0 < -a := neg_pos_of_neg hneg
    have hp := OrderedField.mul_pos hpos hpos
    rw [neg_mul_neg] at hp
    exact hp

theorem zero_lt_one : (0 : F) < 1 := by
  have h := sq_pos_of_ne_zero (CommField.zero_ne_one (α := F)).symm
  rwa [CommField.one_mul] at h

theorem two_pos : (0 : F) < (1 + 1 : F) := add_pos (zero_lt_one (F := F)) (zero_lt_one (F := F))

theorem inv_pos_of_pos {a : F} (ha : 0 < a) : 0 < FieldOps.inv a := by
  rcases OrderedField.le_total (FieldOps.inv a) 0 with hle | hle
  · exfalso
    have hmul : a * FieldOps.inv a ≤ 0 := by
      rw [CommField.mul_comm]
      exact mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt ha)
    rw [CommField.mul_inv_cancel a (ne_of_gt ha)] at hmul
    exact not_le_of_lt (zero_lt_one (F := F)) hmul
  · refine lt_of_le_not_le hle ?_
    intro hle0
    have heq : FieldOps.inv a = 0 := OrderedField.le_antisymm hle0 hle
    have h1 := CommField.mul_inv_cancel a (ne_of_gt ha)
    rw [heq, mul_zero] at h1
    exact CommField.zero_ne_one h1

theorem div_pos {a b : F} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  OrderedField.mul_pos ha (inv_pos_of_pos hb)

theorem div_nonneg {a b : F} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  OrderedField.mul_nonneg ha (le_of_lt (inv_pos_of_pos hb))

theorem lt_div_iff_of_pos {a b c : F} (hc : 0 < c) : a < b / c ↔ a * c < b := by
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_right h hc
    rwa [div_mul_cancel b (ne_of_gt hc)] at h1
  · intro h
    have h1 := mul_lt_mul_of_pos_right h (inv_pos_of_pos hc)
    change (a * c) * FieldOps.inv c < b / c at h1
    rwa [CommField.mul_assoc, CommField.mul_inv_cancel c (ne_of_gt hc), mul_one] at h1

theorem le_div_iff_of_pos {a b c : F} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt hc)
    rwa [div_mul_cancel b (ne_of_gt hc)] at h1
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos_of_pos hc))
    change (a * c) * FieldOps.inv c ≤ b / c at h1
    rwa [CommField.mul_assoc, CommField.mul_inv_cancel c (ne_of_gt hc), mul_one] at h1

theorem div_le_iff_of_pos {a b c : F} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt hb)
    rwa [div_mul_cancel a (ne_of_gt hb)] at h1
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos_of_pos hb))
    change a / b ≤ (c * b) * FieldOps.inv b at h1
    rwa [CommField.mul_assoc, CommField.mul_inv_cancel b (ne_of_gt hb), mul_one] at h1

theorem div_lt_iff_of_pos {a b c : F} (hb : 0 < b) : a / b < c ↔ a < c * b := by
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_right h hb
    rwa [div_mul_cancel a (ne_of_gt hb)] at h1
  · intro h
    have h1 := mul_lt_mul_of_pos_right h (inv_pos_of_pos hb)
    change a / b < (c * b) * FieldOps.inv b at h1
    rwa [CommField.mul_assoc, CommField.mul_inv_cancel b (ne_of_gt hb), mul_one] at h1

end OrderedFieldLemmas

/-! ### Exact Computable Rational Field `Q` -/

structure QRaw where
  num : Int
  den : Nat
  den_pos : 0 < den

def qEq (a b : QRaw) : Prop := a.num * (b.den : Int) = b.num * (a.den : Int)

theorem qEq_refl (a : QRaw) : qEq a a := rfl
theorem qEq_symm {a b : QRaw} (h : qEq a b) : qEq b a := h.symm
theorem qEq_trans {a b c : QRaw} (hab : qEq a b) (hbc : qEq b c) : qEq a c := by
  unfold qEq at *
  have hb : (b.den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt b.den_pos)
  have h1 : a.num * (c.den : Int) * (b.den : Int) = b.num * (a.den : Int) * (c.den : Int) := by
    rw [Int.mul_right_comm, hab]
  have h2 : c.num * (a.den : Int) * (b.den : Int) = b.num * (a.den : Int) * (c.den : Int) := by
    rw [Int.mul_right_comm, ← hbc, Int.mul_right_comm]
  exact Int.eq_of_mul_eq_mul_right hb (h1.trans h2.symm)

instance qSetoid : Setoid QRaw where
  r := qEq
  iseqv := ⟨qEq_refl, qEq_symm, qEq_trans⟩

def Q : Type := Quotient qSetoid

def mkQ (n : Int) (d : Nat) (hd : 0 < d := by decide) : Q :=
  Quotient.mk qSetoid ⟨n, d, hd⟩

private def qAddRaw (a b : QRaw) : QRaw :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

private def qNegRaw (a : QRaw) : QRaw :=
  ⟨-a.num, a.den, a.den_pos⟩

private def qMulRaw (a b : QRaw) : QRaw :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

private def qInvRaw (a : QRaw) : QRaw :=
  if h : a.num > 0 then ⟨(a.den : Int), a.num.natAbs, Int.natAbs_pos.mpr (Int.ne_of_gt h)⟩
  else if h2 : a.num < 0 then ⟨-(a.den : Int), a.num.natAbs, Int.natAbs_pos.mpr (Int.ne_of_lt h2)⟩
  else ⟨0, 1, Nat.zero_lt_one⟩

private def qLeRaw (a b : QRaw) : Prop := a.num * (b.den : Int) ≤ b.num * (a.den : Int)
private def qLtRaw (a b : QRaw) : Prop := a.num * (b.den : Int) < b.num * (a.den : Int)

private theorem int_swap4 (a b c d : Int) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Int.mul_assoc, Int.mul_left_comm b c d, ← Int.mul_assoc]

private theorem qAddRaw_resp {a1 a2 b1 b2 : QRaw} (ha : qEq a1 a2) (hb : qEq b1 b2) :
    qEq (qAddRaw a1 b1) (qAddRaw a2 b2) := by
  unfold qEq qAddRaw at *
  dsimp
  have h1 : a1.num * (b1.den : Int) * ((a2.den : Int) * (b2.den : Int))
      = a2.num * (b2.den : Int) * ((a1.den : Int) * (b1.den : Int)) := by
    calc a1.num * ↑b1.den * (↑a2.den * ↑b2.den)
        = (a1.num * ↑a2.den) * (↑b1.den * ↑b2.den) := int_swap4 _ _ _ _
      _ = (a2.num * ↑a1.den) * (↑b2.den * ↑b1.den) := by rw [ha, Int.mul_comm (b1.den : Int) (b2.den : Int)]
      _ = (a2.num * ↑b2.den) * (↑a1.den * ↑b1.den) := int_swap4 _ _ _ _
  have h2 : b1.num * (a1.den : Int) * ((a2.den : Int) * (b2.den : Int))
      = b2.num * (a2.den : Int) * ((a1.den : Int) * (b1.den : Int)) := by
    calc b1.num * ↑a1.den * (↑a2.den * ↑b2.den)
        = (b1.num * ↑b2.den) * (↑a1.den * ↑a2.den) := by
          rw [Int.mul_comm (a2.den : Int) (b2.den : Int), int_swap4]
      _ = (b2.num * ↑b1.den) * (↑a2.den * ↑a1.den) := by rw [hb, Int.mul_comm (a1.den : Int) (a2.den : Int)]
      _ = (b2.num * ↑a2.den) * (↑a1.den * ↑b1.den) := by
          rw [int_swap4, Int.mul_comm (b1.den : Int) (a1.den : Int)]
  show (a1.num * (b1.den : Int) + b1.num * (a1.den : Int)) * ((a2.den * b2.den : Nat) : Int)
     = (a2.num * (b2.den : Int) + b2.num * (a2.den : Int)) * ((a1.den * b1.den : Nat) : Int)
  rw [Int.natCast_mul, Int.natCast_mul, Int.add_mul, Int.add_mul, h1, h2]

private theorem qNegRaw_resp {a1 a2 : QRaw} (ha : qEq a1 a2) : qEq (qNegRaw a1) (qNegRaw a2) := by
  unfold qEq qNegRaw at *
  dsimp
  rw [Int.neg_mul, Int.neg_mul, ha]

private theorem qMulRaw_resp {a1 a2 b1 b2 : QRaw} (ha : qEq a1 a2) (hb : qEq b1 b2) :
    qEq (qMulRaw a1 b1) (qMulRaw a2 b2) := by
  unfold qEq qMulRaw at *
  dsimp
  rw [Int.natCast_mul, Int.natCast_mul, int_swap4, ha, hb, ← int_swap4]

private theorem natAbs_of_pos_int {x : Int} (h : x > 0) : (x.natAbs : Int) = x :=
  Int.natAbs_of_nonneg (Int.le_of_lt h)

private theorem natAbs_of_neg_int {x : Int} (h : x < 0) : (x.natAbs : Int) = -x := by
  have h1 : -x ≥ 0 := Int.le_of_lt (Int.neg_pos_of_neg h)
  have h2 : (-x).natAbs = x.natAbs := Int.natAbs_neg x
  rw [← h2, Int.natAbs_of_nonneg h1]

private theorem qInvRaw_resp {a1 a2 : QRaw} (ha : qEq a1 a2) : qEq (qInvRaw a1) (qInvRaw a2) := by
  unfold qEq at ha
  have d1 : (0 : Int) < (a1.den : Int) := Int.ofNat_pos.mpr a1.den_pos
  have d2 : (0 : Int) < (a2.den : Int) := Int.ofNat_pos.mpr a2.den_pos
  unfold qInvRaw
  by_cases h1p : a1.num > 0
  · have h2p : a2.num > 0 := by
      have hp : 0 < a2.num * (a1.den : Int) := ha ▸ Int.mul_pos h1p d2
      rcases Int.lt_trichotomy a2.num 0 with hlt | heq | hgt
      · have hnp : a2.num * (a1.den : Int) < 0 := Int.mul_neg_of_neg_of_pos hlt d1
        omega
      · rw [heq, Int.zero_mul] at hp; omega
      · exact hgt
    rw [dif_pos h1p, dif_pos h2p]
    unfold qEq; dsimp
    rw [natAbs_of_pos_int h1p, natAbs_of_pos_int h2p,
        Int.mul_comm (a1.den : Int) a2.num, Int.mul_comm (a2.den : Int) a1.num, ha]
  · by_cases h1n : a1.num < 0
    · have h2np : ¬ (a2.num > 0) := by
        intro h2p
        have hn : a1.num * (a2.den : Int) < 0 := Int.mul_neg_of_neg_of_pos h1n d2
        have hp : 0 < a2.num * (a1.den : Int) := Int.mul_pos h2p d1
        rw [ha] at hn
        omega
      have h2n : a2.num < 0 := by
        have hn : a2.num * (a1.den : Int) < 0 := ha ▸ Int.mul_neg_of_neg_of_pos h1n d2
        rcases Int.lt_trichotomy a2.num 0 with hlt | heq | hgt
        · exact hlt
        · rw [heq, Int.zero_mul] at hn; omega
        · have hp : 0 < a2.num * (a1.den : Int) := Int.mul_pos hgt d1
          omega
      rw [dif_neg h1p, dif_pos h1n, dif_neg h2np, dif_pos h2n]
      unfold qEq; dsimp
      rw [natAbs_of_neg_int h1n, natAbs_of_neg_int h2n,
          Int.neg_mul, Int.mul_neg, Int.neg_mul, Int.mul_neg,
          Int.mul_comm (a1.den : Int) a2.num, Int.mul_comm (a2.den : Int) a1.num, ha]
    · have h1z : a1.num = 0 := by omega
      have h2z : a2.num = 0 := by
        rw [h1z, Int.zero_mul] at ha
        exact (Int.mul_eq_zero.mp ha.symm).resolve_right (Int.ne_of_gt d1)
      have h2p : ¬ (a2.num > 0) := by omega
      have h2n : ¬ (a2.num < 0) := by omega
      rw [dif_neg h1p, dif_neg h1n, dif_neg h2p, dif_neg h2n]
      rfl

private theorem qLeRaw_resp {a1 a2 b1 b2 : QRaw} (ha : qEq a1 a2) (hb : qEq b1 b2) :
    qLeRaw a1 b1 = qLeRaw a2 b2 := by
  unfold qEq at ha hb
  unfold qLeRaw
  have d1a : (0 : Int) < a1.den := Int.ofNat_pos.mpr a1.den_pos
  have d2a : (0 : Int) < a2.den := Int.ofNat_pos.mpr a2.den_pos
  have d1b : (0 : Int) < b1.den := Int.ofNat_pos.mpr b1.den_pos
  have d2b : (0 : Int) < b2.den := Int.ofNat_pos.mpr b2.den_pos
  apply propext
  constructor
  · intro h
    have h1 : a1.num * (b1.den : Int) * ((a2.den : Int) * (b2.den : Int))
        ≤ b1.num * (a1.den : Int) * ((a2.den : Int) * (b2.den : Int)) :=
      Int.mul_le_mul_of_nonneg_right h (Int.mul_nonneg (Int.le_of_lt d2a) (Int.le_of_lt d2b))
    have lhs_eq : a1.num * (b1.den : Int) * ((a2.den : Int) * (b2.den : Int))
        = a2.num * (b2.den : Int) * ((a1.den : Int) * (b1.den : Int)) := by
      calc a1.num * ↑b1.den * (↑a2.den * ↑b2.den)
          = (a1.num * ↑a2.den) * (↑b1.den * ↑b2.den) := int_swap4 _ _ _ _
        _ = (a2.num * ↑a1.den) * (↑b2.den * ↑b1.den) := by rw [ha, Int.mul_comm (b1.den : Int) (b2.den : Int)]
        _ = (a2.num * ↑b2.den) * (↑a1.den * ↑b1.den) := int_swap4 _ _ _ _
    have rhs_eq : b1.num * (a1.den : Int) * ((a2.den : Int) * (b2.den : Int))
        = b2.num * (a2.den : Int) * ((a1.den : Int) * (b1.den : Int)) := by
      calc b1.num * ↑a1.den * (↑a2.den * ↑b2.den)
          = (b1.num * ↑b2.den) * (↑a1.den * ↑a2.den) := by
            rw [Int.mul_comm (a2.den : Int) (b2.den : Int), int_swap4]
        _ = (b2.num * ↑b1.den) * (↑a2.den * ↑a1.den) := by rw [hb, Int.mul_comm (a1.den : Int) (a2.den : Int)]
        _ = (b2.num * ↑a2.den) * (↑a1.den * ↑b1.den) := by
            rw [int_swap4, Int.mul_comm (b1.den : Int) (a1.den : Int)]
    rw [lhs_eq, rhs_eq] at h1
    exact Int.le_of_mul_le_mul_right h1 (Int.mul_pos d1a d1b)
  · intro h
    have h1 : a2.num * (b2.den : Int) * ((a1.den : Int) * (b1.den : Int))
        ≤ b2.num * (a2.den : Int) * ((a1.den : Int) * (b1.den : Int)) :=
      Int.mul_le_mul_of_nonneg_right h (Int.mul_nonneg (Int.le_of_lt d1a) (Int.le_of_lt d1b))
    have lhs_eq : a2.num * (b2.den : Int) * ((a1.den : Int) * (b1.den : Int))
        = a1.num * (b1.den : Int) * ((a2.den : Int) * (b2.den : Int)) := by
      calc a2.num * ↑b2.den * (↑a1.den * ↑b1.den)
          = (a2.num * ↑a1.den) * (↑b2.den * ↑b1.den) := int_swap4 _ _ _ _
        _ = (a1.num * ↑a2.den) * (↑b1.den * ↑b2.den) := by rw [← ha, Int.mul_comm (b2.den : Int) (b1.den : Int)]
        _ = (a1.num * ↑b1.den) * (↑a2.den * ↑b2.den) := int_swap4 _ _ _ _
    have rhs_eq : b2.num * (a2.den : Int) * ((a1.den : Int) * (b1.den : Int))
        = b1.num * (a1.den : Int) * ((a2.den : Int) * (b2.den : Int)) := by
      calc b2.num * ↑a2.den * (↑a1.den * ↑b1.den)
          = (b2.num * ↑b1.den) * (↑a2.den * ↑a1.den) := by
            rw [Int.mul_comm (a1.den : Int) (b1.den : Int), int_swap4]
        _ = (b1.num * ↑b2.den) * (↑a1.den * ↑a2.den) := by rw [← hb, Int.mul_comm (a2.den : Int) (a1.den : Int)]
        _ = (b1.num * ↑a1.den) * (↑a2.den * ↑b2.den) := by
            rw [int_swap4, Int.mul_comm (b2.den : Int) (a2.den : Int)]
    rw [lhs_eq, rhs_eq] at h1
    exact Int.le_of_mul_le_mul_right h1 (Int.mul_pos d2a d2b)

private theorem qLtRaw_resp {a1 a2 b1 b2 : QRaw} (ha : qEq a1 a2) (hb : qEq b1 b2) :
    qLtRaw a1 b1 = qLtRaw a2 b2 := by
  have hle1 : qLeRaw b1 a1 = qLeRaw b2 a2 := qLeRaw_resp hb ha
  have hle2 : qLeRaw a1 b1 = qLeRaw a2 b2 := qLeRaw_resp ha hb
  have e1 : qLtRaw a1 b1 ↔ (qLeRaw a1 b1 ∧ ¬ qLeRaw b1 a1) := by unfold qLtRaw qLeRaw; omega
  have e2 : qLtRaw a2 b2 ↔ (qLeRaw a2 b2 ∧ ¬ qLeRaw b2 a2) := by unfold qLtRaw qLeRaw; omega
  exact propext (by rw [e1, e2, hle1, hle2])

def qAdd : Q → Q → Q := Quotient.lift₂ (fun a b => Quotient.mk qSetoid (qAddRaw a b)) (fun _ _ _ _ ha hb => Quotient.sound (qAddRaw_resp ha hb))
def qNeg : Q → Q := Quotient.lift (fun a => Quotient.mk qSetoid (qNegRaw a)) (fun _ _ ha => Quotient.sound (qNegRaw_resp ha))
def qMul : Q → Q → Q := Quotient.lift₂ (fun a b => Quotient.mk qSetoid (qMulRaw a b)) (fun _ _ _ _ ha hb => Quotient.sound (qMulRaw_resp ha hb))
def qInv : Q → Q := Quotient.lift (fun a => Quotient.mk qSetoid (qInvRaw a)) (fun _ _ ha => Quotient.sound (qInvRaw_resp ha))
def qLe : Q → Q → Prop := Quotient.lift₂ qLeRaw (fun _ _ _ _ ha hb => qLeRaw_resp ha hb)
def qLt : Q → Q → Prop := Quotient.lift₂ qLtRaw (fun _ _ _ _ ha hb => qLtRaw_resp ha hb)

instance : FieldOps Q where
  zero := mkQ 0 1
  one := mkQ 1 1
  add := qAdd
  neg := qNeg
  mul := qMul
  inv := qInv

private theorem q_add_assoc (a b c : Q) : (a + b) + c = a + (b + c) := by
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  induction c using Quotient.ind with | _ c =>
  apply Quotient.sound
  show qEq (qAddRaw (qAddRaw a b) c) (qAddRaw a (qAddRaw b c))
  unfold qEq qAddRaw
  dsimp
  simp only [Int.natCast_mul]
  have t2 : (b.num * ↑a.den) * ↑c.den + c.num * (↑a.den * ↑b.den)
      = (b.num * ↑c.den + c.num * ↑b.den) * ↑a.den := by
    rw [Int.add_mul, Int.mul_right_comm b.num ↑a.den ↑c.den,
        Int.mul_comm c.num (↑a.den * ↑b.den), Int.mul_assoc ↑a.den ↑b.den c.num,
        Int.mul_comm ↑a.den (↑b.den * c.num), Int.mul_comm ↑b.den c.num]
  have h : (a.num * ↑b.den + b.num * ↑a.den) * ↑c.den + c.num * (↑a.den * ↑b.den)
      = a.num * (↑b.den * ↑c.den) + (b.num * ↑c.den + c.num * ↑b.den) * ↑a.den := by
    rw [Int.add_mul, Int.add_assoc, Int.mul_assoc a.num ↑b.den ↑c.den, t2]
  rw [h, Int.mul_assoc (a.den : Int) (b.den : Int) (c.den : Int)]

private theorem q_add_comm (a b : Q) : a + b = b + a := by
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  apply Quotient.sound
  show qEq (qAddRaw a b) (qAddRaw b a)
  unfold qEq qAddRaw
  dsimp
  rw [Int.natCast_mul, Int.natCast_mul, Int.add_comm (a.num * ↑b.den), Int.mul_comm (a.den : Int) (b.den : Int)]

private theorem q_zero_add (a : Q) : (0 : Q) + a = a := by
  induction a using Quotient.ind with | _ a =>
  apply Quotient.sound
  show qEq (qAddRaw ⟨0, 1, Nat.zero_lt_one⟩ a) a
  unfold qEq qAddRaw
  dsimp
  rw [Int.natCast_mul]
  change (0 * ↑a.den + a.num * 1) * ↑a.den = a.num * (1 * ↑a.den)
  simp only [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]

private theorem q_add_neg_cancel (a : Q) : a + (-a) = 0 := by
  induction a using Quotient.ind with | _ a =>
  apply Quotient.sound
  show qEq (qAddRaw a (qNegRaw a)) ⟨0, 1, Nat.zero_lt_one⟩
  unfold qEq qAddRaw qNegRaw
  dsimp
  rw [Int.neg_mul, Int.add_right_neg, Int.zero_mul, Int.zero_mul]

private theorem q_mul_assoc (a b c : Q) : (a * b) * c = a * (b * c) := by
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  induction c using Quotient.ind with | _ c =>
  apply Quotient.sound
  show qEq (qMulRaw (qMulRaw a b) c) (qMulRaw a (qMulRaw b c))
  unfold qEq qMulRaw
  dsimp
  simp only [Int.natCast_mul]
  rw [Int.mul_assoc a.num b.num c.num, Int.mul_assoc (a.den : Int) (b.den : Int) (c.den : Int)]

private theorem q_mul_comm (a b : Q) : a * b = b * a := by
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  apply Quotient.sound
  show qEq (qMulRaw a b) (qMulRaw b a)
  unfold qEq qMulRaw
  dsimp
  rw [Int.natCast_mul, Int.natCast_mul, Int.mul_comm a.num b.num, Int.mul_comm (a.den : Int) (b.den : Int)]

private theorem q_one_mul (a : Q) : (1 : Q) * a = a := by
  induction a using Quotient.ind with | _ a =>
  apply Quotient.sound
  show qEq (qMulRaw ⟨1, 1, Nat.zero_lt_one⟩ a) a
  unfold qEq qMulRaw
  dsimp
  rw [Int.natCast_mul]
  change (1 * a.num) * ↑a.den = a.num * (1 * ↑a.den)
  simp only [Int.one_mul]

private theorem q_left_distrib (a b c : Q) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  induction c using Quotient.ind with | _ c =>
  apply Quotient.sound
  show qEq (qMulRaw a (qAddRaw b c)) (qAddRaw (qMulRaw a b) (qMulRaw a c))
  unfold qEq qAddRaw qMulRaw
  dsimp
  simp only [Int.natCast_mul]
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  have t1 : a.num * (b.num * ↑c.den) * (↑a.den * ↑b.den * (↑a.den * ↑c.den))
      = a.num * b.num * (↑a.den * ↑c.den) * (↑a.den * (↑b.den * ↑c.den)) := by
    calc a.num * (b.num * ↑c.den) * (↑a.den * ↑b.den * (↑a.den * ↑c.den))
        = (a.num * b.num) * (↑c.den * (↑a.den * ↑b.den * (↑a.den * ↑c.den))) := by
          rw [← Int.mul_assoc a.num b.num ↑c.den, Int.mul_assoc (a.num * b.num)]
      _ = (a.num * b.num) * ((↑a.den * ↑c.den) * (↑a.den * (↑b.den * ↑c.den))) := by
          apply congrArg (fun w => (a.num * b.num) * w)
          rw [Int.mul_comm ↑c.den (↑a.den * ↑b.den * (↑a.den * ↑c.den)),
              Int.mul_comm (↑a.den * ↑b.den) (↑a.den * ↑c.den),
              Int.mul_assoc (↑a.den * ↑c.den), Int.mul_assoc ↑a.den ↑b.den ↑c.den]
      _ = a.num * b.num * (↑a.den * ↑c.den) * (↑a.den * (↑b.den * ↑c.den)) := by
          rw [← Int.mul_assoc]
  have t2 : a.num * (c.num * ↑b.den) * (↑a.den * ↑b.den * (↑a.den * ↑c.den))
      = a.num * c.num * (↑a.den * ↑b.den) * (↑a.den * (↑b.den * ↑c.den)) := by
    calc a.num * (c.num * ↑b.den) * (↑a.den * ↑b.den * (↑a.den * ↑c.den))
        = (a.num * c.num) * (↑b.den * (↑a.den * ↑b.den * (↑a.den * ↑c.den))) := by
          rw [← Int.mul_assoc a.num c.num ↑b.den, Int.mul_assoc (a.num * c.num)]
      _ = (a.num * c.num) * ((↑a.den * ↑b.den) * (↑a.den * (↑b.den * ↑c.den))) := by
          apply congrArg (fun w => (a.num * c.num) * w)
          rw [Int.mul_comm ↑b.den (↑a.den * ↑b.den * (↑a.den * ↑c.den)),
              Int.mul_assoc (↑a.den * ↑b.den), Int.mul_assoc ↑a.den ↑c.den ↑b.den,
              Int.mul_comm ↑c.den ↑b.den]
      _ = a.num * c.num * (↑a.den * ↑b.den) * (↑a.den * (↑b.den * ↑c.den)) := by
          rw [← Int.mul_assoc]
  rw [t1, t2]

private theorem q_mul_inv_cancel (a : Q) (ha : a ≠ 0) : a * FieldOps.inv a = 1 := by
  induction a using Quotient.ind with | _ a =>
  apply Quotient.sound
  have hnz : a.num ≠ 0 := by
    intro hz
    apply ha
    apply Quotient.sound
    show qEq a ⟨0, 1, Nat.zero_lt_one⟩
    unfold qEq
    dsimp
    rw [hz, Int.zero_mul, Int.zero_mul]
  show qEq (qMulRaw a (qInvRaw a)) ⟨1, 1, Nat.zero_lt_one⟩
  unfold qEq qMulRaw qInvRaw
  dsimp
  rw [Int.natCast_mul]
  by_cases hp : a.num > 0
  · rw [dif_pos hp]; dsimp
    rw [natAbs_of_pos_int hp]
    change (a.num * ↑a.den) * 1 = 1 * (↑a.den * a.num)
    rw [Int.mul_one, Int.one_mul, Int.mul_comm a.num (a.den : Int)]
  · have hn : a.num < 0 := by omega
    rw [dif_neg hp, dif_pos hn]; dsimp
    rw [natAbs_of_neg_int hn]
    change (a.num * -↑a.den) * 1 = 1 * (↑a.den * -a.num)
    rw [Int.mul_one, Int.one_mul, Int.mul_neg, Int.mul_neg, Int.mul_comm a.num (a.den : Int)]

private theorem q_inv_zero : FieldOps.inv (0 : Q) = 0 := by
  apply Quotient.sound
  show qEq (qInvRaw ⟨0, 1, Nat.zero_lt_one⟩) ⟨0, 1, Nat.zero_lt_one⟩
  unfold qEq qInvRaw
  decide

private theorem q_zero_ne_one : (0 : Q) ≠ 1 := by
  intro h
  have h1 : qEq ⟨0, 1, Nat.zero_lt_one⟩ ⟨1, 1, Nat.zero_lt_one⟩ := Quotient.exact h
  unfold qEq at h1
  dsimp at h1
  omega

instance : OrderedField Q where
  add_assoc := q_add_assoc
  add_comm := q_add_comm
  zero_add := q_zero_add
  add_neg_cancel := q_add_neg_cancel
  mul_assoc := q_mul_assoc
  mul_comm := q_mul_comm
  one_mul := q_one_mul
  left_distrib := q_left_distrib
  mul_inv_cancel := q_mul_inv_cancel
  inv_zero := q_inv_zero
  zero_ne_one := q_zero_ne_one
  le := qLe
  lt := qLt
  le_refl a := by
    induction a using Quotient.ind with | _ a =>
    exact Int.le_refl _
  le_trans {a b c} h1 h2 := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    induction c using Quotient.ind with | _ c =>
    unfold qLe qLeRaw at *
    have da : (0 : Int) < a.den := Int.ofNat_pos.mpr a.den_pos
    have db : (0 : Int) < b.den := Int.ofNat_pos.mpr b.den_pos
    have dc : (0 : Int) < c.den := Int.ofNat_pos.mpr c.den_pos
    have m1 : a.num * ↑b.den * ↑c.den ≤ b.num * ↑a.den * ↑c.den :=
      Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt dc)
    have m2 : b.num * ↑c.den * ↑a.den ≤ c.num * ↑b.den * ↑a.den :=
      Int.mul_le_mul_of_nonneg_right h2 (Int.le_of_lt da)
    rw [Int.mul_right_comm b.num ↑c.den ↑a.den] at m2
    have m3 := Int.le_trans m1 m2
    rw [Int.mul_right_comm a.num ↑b.den ↑c.den, Int.mul_right_comm c.num ↑b.den ↑a.den] at m3
    exact Int.le_of_mul_le_mul_right m3 db
  le_antisymm {a b} h1 h2 := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    apply Quotient.sound
    show qEq a b
    unfold qEq
    unfold qLe qLeRaw at h1 h2
    exact Int.le_antisymm h1 h2
  le_total a b := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    exact Int.le_total _ _
  lt_iff_le_not_le a b := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    show qLtRaw a b ↔ qLeRaw a b ∧ ¬ qLeRaw b a
    unfold qLtRaw qLeRaw
    omega
  add_le_add_left {a b} c h := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    induction c using Quotient.ind with | _ c =>
    unfold qLe qLeRaw at h
    show qLeRaw (qAddRaw c a) (qAddRaw c b)
    unfold qLeRaw qAddRaw
    dsimp
    rw [Int.natCast_mul, Int.natCast_mul]
    have dc : (0 : Int) < c.den := Int.ofNat_pos.mpr c.den_pos
    have hd : a.num * ↑b.den * (↑c.den * ↑c.den) ≤ b.num * ↑a.den * (↑c.den * ↑c.den) :=
      Int.mul_le_mul_of_nonneg_right h (Int.mul_nonneg (Int.le_of_lt dc) (Int.le_of_lt dc))
    have lhs_eq : (c.num * ↑a.den + a.num * ↑c.den) * (↑c.den * ↑b.den)
        = c.num * ↑c.den * (↑a.den * ↑b.den) + a.num * ↑b.den * (↑c.den * ↑c.den) := by
      rw [Int.add_mul, int_swap4 c.num ↑a.den ↑c.den ↑b.den,
          Int.mul_comm (↑c.den : Int) ↑b.den, int_swap4 a.num ↑c.den ↑b.den ↑c.den]
    have rhs_eq : (c.num * ↑b.den + b.num * ↑c.den) * (↑c.den * ↑a.den)
        = c.num * ↑c.den * (↑a.den * ↑b.den) + b.num * ↑a.den * (↑c.den * ↑c.den) := by
      rw [Int.add_mul, int_swap4 c.num ↑b.den ↑c.den ↑a.den, Int.mul_comm ↑b.den ↑a.den,
          Int.mul_comm (↑c.den : Int) ↑a.den, int_swap4 b.num ↑c.den ↑a.den ↑c.den]
    rw [lhs_eq, rhs_eq]
    exact Int.add_le_add_left hd _
  mul_nonneg {a b} ha hb := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    unfold qLe qLeRaw at ha hb
    change 0 * (a.den : Int) ≤ a.num * 1 at ha
    change 0 * (b.den : Int) ≤ b.num * 1 at hb
    rw [Int.zero_mul, Int.mul_one] at ha hb
    show qLeRaw ⟨0, 1, Nat.zero_lt_one⟩ (qMulRaw a b)
    unfold qLeRaw qMulRaw
    dsimp
    rw [Int.natCast_mul]
    change 0 * (↑a.den * ↑b.den) ≤ a.num * b.num * 1
    rw [Int.zero_mul, Int.mul_one]
    exact Int.mul_nonneg ha hb
  mul_pos {a b} ha hb := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    unfold qLt qLtRaw at ha hb
    change 0 * (a.den : Int) < a.num * 1 at ha
    change 0 * (b.den : Int) < b.num * 1 at hb
    rw [Int.zero_mul, Int.mul_one] at ha hb
    show qLtRaw ⟨0, 1, Nat.zero_lt_one⟩ (qMulRaw a b)
    unfold qLtRaw qMulRaw
    dsimp
    rw [Int.natCast_mul]
    change 0 * (↑a.den * ↑b.den) < a.num * b.num * 1
    rw [Int.zero_mul, Int.mul_one]
    exact Int.mul_pos ha hb

theorem mkQ_add (n1 n2 : Int) (d1 d2 : Nat) (h1 : 0 < d1) (h2 : 0 < d2) :
    mkQ n1 d1 h1 + mkQ n2 d2 h2 = mkQ (n1 * d2 + n2 * d1) (d1 * d2) (Nat.mul_pos h1 h2) := rfl

theorem mkQ_neg (n : Int) (d : Nat) (h : 0 < d) :
    -(mkQ n d h) = mkQ (-n) d h := rfl

theorem mkQ_mul (n1 n2 : Int) (d1 d2 : Nat) (h1 : 0 < d1) (h2 : 0 < d2) :
    mkQ n1 d1 h1 * mkQ n2 d2 h2 = mkQ (n1 * n2) (d1 * d2) (Nat.mul_pos h1 h2) := rfl

theorem mkQ_lt_of {n1 n2 : Int} {d1 d2 : Nat} {h1 : 0 < d1} {h2 : 0 < d2}
    (h : n1 * (d2 : Int) < n2 * (d1 : Int)) : mkQ n1 d1 h1 < mkQ n2 d2 h2 := h

theorem mkQ_le_of {n1 n2 : Int} {d1 d2 : Nat} {h1 : 0 < d1} {h2 : 0 < d2}
    (h : n1 * (d2 : Int) ≤ n2 * (d1 : Int)) : mkQ n1 d1 h1 ≤ mkQ n2 d2 h2 := h

theorem mkQ_eq_of {n1 n2 : Int} {d1 d2 : Nat} {h1 : 0 < d1} {h2 : 0 < d2}
    (h : n1 * (d2 : Int) = n2 * (d1 : Int)) : mkQ n1 d1 h1 = mkQ n2 d2 h2 :=
  Quotient.sound h

theorem mkQ_zero_eq : (0 : Q) = mkQ 0 1 := rfl
theorem mkQ_one_eq : (1 : Q) = mkQ 1 1 := rfl

/-! ## Part II: Complex Algebra `C2` & Hankel Branch-Cut Spectral Identities -/

structure C2 (F : Type) where
  re : F
  im : F

section ComplexAlgebra

variable {F : Type} [CommField F]

def cOfReal (x : F) : C2 F := ⟨x, 0⟩
def cAdd (a b : C2 F) : C2 F := ⟨a.re + b.re, a.im + b.im⟩
def cNeg (a : C2 F) : C2 F := ⟨-a.re, -a.im⟩
def cSub (a b : C2 F) : C2 F := ⟨a.re - b.re, a.im - b.im⟩
def cMul (a b : C2 F) : C2 F := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def cConj (a : C2 F) : C2 F := ⟨a.re, -a.im⟩
def cNormSq (a : C2 F) : F := a.re * a.re + a.im * a.im
def cScale (s : F) (a : C2 F) : C2 F := ⟨s * a.re, s * a.im⟩

theorem cMul_conj_re (a : C2 F) : (cMul a (cConj a)).re = cNormSq a := by
  unfold cMul cConj cNormSq
  dsimp
  rw [mul_neg, sub_def, neg_neg]

theorem cMul_conj_im (a : C2 F) : (cMul a (cConj a)).im = 0 := by
  unfold cMul cConj
  dsimp
  rw [mul_neg, CommField.mul_comm a.im a.re, neg_add_cancel]

theorem cConj_add (a b : C2 F) : cConj (cAdd a b) = cAdd (cConj a) (cConj b) := by
  unfold cConj cAdd
  dsimp
  rw [neg_add]

theorem cConj_mul (a b : C2 F) : cConj (cMul a b) = cMul (cConj a) (cConj b) := by
  unfold cConj cMul
  dsimp
  have hre : a.re * b.re - a.im * b.im = a.re * b.re - (-a.im) * (-b.im) := by
    rw [neg_mul_neg]
  have him : -(a.re * b.im + a.im * b.re) = a.re * (-b.im) + (-a.im) * b.re := by
    rw [mul_neg, neg_mul, neg_add]
  rw [hre, him]

theorem cMul_add (a b c : C2 F) : cMul a (cAdd b c) = cAdd (cMul a b) (cMul a c) := by
  unfold cMul cAdd
  dsimp
  have hre : a.re * (b.re + c.re) - a.im * (b.im + c.im)
      = (a.re * b.re - a.im * b.im) + (a.re * c.re - a.im * c.im) := by
    rw [CommField.left_distrib, CommField.left_distrib, sub_def, sub_def, sub_def, neg_add,
        CommField.add_assoc, add_left_comm (a.re * c.re) (-(a.im * b.im)), ← CommField.add_assoc]
  have him : a.re * (b.im + c.im) + a.im * (b.re + c.re)
      = (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re) := by
    rw [CommField.left_distrib, CommField.left_distrib,
        CommField.add_assoc, add_left_comm (a.re * c.im) (a.im * b.re), ← CommField.add_assoc]
  rw [hre, him]

/--
  Algebraic polynomial `w(z, g) = z^2 + 2 g z = z (z + 2g)` and denominator
  `D(z, g) = z^2 + 2 g z + 1` along the Hankel branch cut `z = r^μ e^{-i π μ}`.
-/
def hankelW (z : C2 F) (g : F) : C2 F :=
  cAdd (cMul z z) (cScale ((1 + 1 : F) * g) z)

def hankelDenom (z : C2 F) (g : F) : C2 F :=
  cAdd (hankelW z g) (cOfReal 1)

theorem hankelW_im (z : C2 F) (g : F) :
    (hankelW z g).im = (1 + 1 : F) * z.im * (z.re + g) := by
  unfold hankelW cAdd cMul cScale
  dsimp
  have h1 : z.re * z.im + z.im * z.re = (1 + 1 : F) * z.im * z.re := by
    rw [CommField.mul_comm z.re z.im, right_distrib, CommField.one_mul, right_distrib]
  have h2 : ((1 + 1 : F) * g) * z.im = (1 + 1 : F) * z.im * g := by
    rw [CommField.mul_assoc, CommField.mul_comm g z.im, ← CommField.mul_assoc]
  rw [h1, h2, ← CommField.left_distrib]

theorem hankelW_eq_factor (z : C2 F) (g : F) :
    hankelW z g = cMul z (cAdd z (cOfReal ((1 + 1 : F) * g))) := by
  unfold hankelW cMul cAdd cOfReal cScale
  dsimp
  have hre : z.re * z.re - z.im * z.im + ((1 + 1 : F) * g) * z.re
      = z.re * (z.re + (1 + 1 : F) * g) - z.im * (z.im + 0) := by
    rw [add_zero, CommField.left_distrib, CommField.mul_comm ((1 + 1 : F) * g) z.re,
        sub_def, sub_def, add_right_comm]
  have him : z.re * z.im + z.im * z.re + ((1 + 1 : F) * g) * z.im
      = z.re * (z.im + 0) + z.im * (z.re + (1 + 1 : F) * g) := by
    rw [add_zero, CommField.left_distrib, CommField.mul_comm ((1 + 1 : F) * g) z.im, CommField.add_assoc]
  rw [hre, him]

/--
  Core Hankel branch-cut discontinuity identity for `G̃_{μ,g}(r e^{-iπ}) = -w / (w + 1)`
  with `w = z^2 + 2 g z` (`z = r^μ e^{-iπμ}`):
  multiplying numerator and denominator by `conj(w + 1)` yields exact numerator
  `Im((-w) * conj(w + 1)) = 2 * (-z.im) * (z.re + g)`,
  corresponding to `2 r^μ sin(πμ) (r^μ cos(πμ) + g)`.
-/
theorem hankel_propagator_numerator_im (z : C2 F) (g : F) :
    (cMul (cNeg (hankelW z g)) (cConj (hankelDenom z g))).im
      = (1 + 1 : F) * (-z.im) * (z.re + g) := by
  let w := hankelW z g
  have hconj : cConj (hankelDenom z g) = cAdd (cConj w) (cOfReal 1) := by
    unfold hankelDenom
    rw [cConj_add]
    unfold cConj cOfReal
    dsimp
    rw [neg_zero]
  have hprod : cMul (cNeg w) (cConj (hankelDenom z g))
      = cAdd (cMul (cNeg w) (cConj w)) (cMul (cNeg w) (cOfReal 1)) := by
    rw [hconj, cMul_add]
  have him1 : (cMul (cNeg w) (cConj w)).im = 0 := by
    unfold cMul cNeg cConj
    dsimp
    rw [neg_mul, mul_neg, neg_mul, neg_neg, CommField.mul_comm w.im w.re, CommField.add_neg_cancel]
  have him2 : (cMul (cNeg w) (cOfReal 1)).im = -w.im := by
    unfold cMul cNeg cOfReal
    dsimp
    rw [mul_zero, mul_one, CommField.zero_add]
  have him_sum : (cMul (cNeg w) (cConj (hankelDenom z g))).im = -w.im := by
    rw [hprod]
    change (cMul (cNeg w) (cConj w)).im + (cMul (cNeg w) (cOfReal 1)).im = -w.im
    rw [him1, him2, CommField.zero_add]
  rw [him_sum]
  change -(hankelW z g).im = (1 + 1 : F) * (-z.im) * (z.re + g)
  rw [hankelW_im, mul_neg, neg_mul]

/--
  Derivative kernel identity for `F̃_{μ,g}(r e^{-iπ}) = 1 / (z^2 + 2 g z + 1)`:
  `Im(conj(w + 1)) = 2 * (-z.im) * (z.re + g)`, identical to the propagator numerator.
-/
theorem hankel_derivative_numerator_im (z : C2 F) (g : F) :
    (cConj (hankelDenom z g)).im = (1 + 1 : F) * (-z.im) * (z.re + g) := by
  unfold hankelDenom
  rw [cConj_add]
  unfold cConj cOfReal
  dsimp
  rw [neg_zero]
  change -(hankelW z g).im + 0 = (1 + 1 : F) * (-z.im) * (z.re + g)
  rw [add_zero, hankelW_im, mul_neg, neg_mul]

theorem hankel_propagator_im_quotient (z : C2 F) (g : F) :
    (cMul (cNeg (hankelW z g)) (cConj (hankelDenom z g))).im / cNormSq (hankelDenom z g)
      = ((1 + 1 : F) * (-z.im) * (z.re + g)) / cNormSq (hankelDenom z g) := by
  rw [hankel_propagator_numerator_im]

theorem hankel_kernel_factor_equality (z : C2 F) (g : F) :
    (cMul (cNeg (hankelW z g)) (cConj (hankelDenom z g))).im
      = (cConj (hankelDenom z g)).im := by
  rw [hankel_propagator_numerator_im, hankel_derivative_numerator_im]

end ComplexAlgebra

section SpectralPositivity

variable {F : Type} [OrderedField F]

/--
  Complete monotonicity regime `μ ∈ (0, 1/2]` (`cos(πμ) ≥ 0`, `sin(πμ) > 0`, `g > 0`):
  the Hankel spectral numerator `2 r^μ sin(πμ) (r^μ cos(πμ) + g)` is strictly positive everywhere.
-/
theorem cm_spectral_numerator_pos {r_mu s_pi c_pi g : F}
    (hr : 0 < r_mu) (hs : 0 < s_pi) (hc : 0 ≤ c_pi) (hg : 0 < g) :
    0 < (1 + 1 : F) * (r_mu * s_pi) * (r_mu * c_pi + g) := by
  have h1 : 0 < (1 + 1 : F) * (r_mu * s_pi) :=
    OrderedField.mul_pos (two_pos (F := F)) (OrderedField.mul_pos hr hs)
  have h2 : 0 < r_mu * c_pi + g :=
    add_pos_of_nonneg_of_pos (OrderedField.mul_nonneg (le_of_lt hr) hc) hg
  exact OrderedField.mul_pos h1 h2

/--
  Non-CM regime `μ ∈ (1/2, 1)` (`cos(πμ) < 0`, `sin(πμ) > 0`, `g > 0`):
  `φ(r)` changes sign uniquely at `r_0^μ = g / (-cos(πμ))`, being strictly positive below `r_0`
  and strictly negative above `r_0`.
-/
theorem single_sign_change_below {r_mu s_pi c_pi g : F}
    (hr : 0 < r_mu) (hs : 0 < s_pi) (hc : c_pi < 0)
    (hlt : r_mu < g / (-c_pi)) :
    0 < (1 + 1 : F) * (r_mu * s_pi) * (r_mu * c_pi + g) := by
  have hnc : 0 < -c_pi := neg_pos_of_neg hc
  have hmul : r_mu * (-c_pi) < g := (lt_div_iff_of_pos hnc).mp hlt
  rw [mul_neg] at hmul
  have hfac : 0 < r_mu * c_pi + g := by
    have hp := sub_pos_of_lt hmul
    rwa [sub_def, neg_neg, CommField.add_comm] at hp
  have h1 : 0 < (1 + 1 : F) * (r_mu * s_pi) :=
    OrderedField.mul_pos (two_pos (F := F)) (OrderedField.mul_pos hr hs)
  exact OrderedField.mul_pos h1 hfac

theorem single_sign_change_at_root {s_pi c_pi g : F} (hc : c_pi < 0) :
    let r0 := g / (-c_pi)
    (1 + 1 : F) * (r0 * s_pi) * (r0 * c_pi + g) = 0 := by
  intro r0
  have hnc : -c_pi ≠ 0 := ne_of_gt (neg_pos_of_neg hc)
  have hmul : r0 * (-c_pi) = g := div_mul_cancel g hnc
  rw [mul_neg] at hmul
  have hz : r0 * c_pi + g = 0 := by
    calc r0 * c_pi + g = -( -(r0 * c_pi) ) + g := by rw [neg_neg]
      _ = -g + g := by rw [hmul]
      _ = 0 := neg_add_cancel g
  rw [hz, mul_zero]

theorem single_sign_change_above {r_mu s_pi c_pi g : F}
    (hr : 0 < r_mu) (hs : 0 < s_pi) (hc : c_pi < 0)
    (hgt : g / (-c_pi) < r_mu) :
    (1 + 1 : F) * (r_mu * s_pi) * (r_mu * c_pi + g) < 0 := by
  have hnc : 0 < -c_pi := neg_pos_of_neg hc
  have hmul : g < r_mu * (-c_pi) := (div_lt_iff_of_pos hnc).mp hgt
  rw [mul_neg] at hmul
  have hneg : r_mu * c_pi + g < 0 := by
    have hp := sub_pos_of_lt hmul
    have hnn := neg_lt_zero_of_pos hp
    have heq : -( -(r_mu * c_pi) - g ) = r_mu * c_pi + g := by
      rw [sub_def, neg_add, neg_neg, neg_neg]
    rwa [heq] at hnn
  have h1 : 0 < (1 + 1 : F) * (r_mu * s_pi) :=
    OrderedField.mul_pos (two_pos (F := F)) (OrderedField.mul_pos hr hs)
  rw [CommField.mul_comm]
  exact mul_neg_of_neg_of_pos hneg h1

end SpectralPositivity

/-! ## Part III: Pole-Equation Root & Phase-Boundary Analysis -/

section PoleBoundary

variable {F : Type} [OrderedField F]

def polePoly (u g : F) : F := u * u + (1 + 1 : F) * g * u + 1

theorem polePoly_complete_square (u g : F) :
    polePoly u g = (u + g) * (u + g) + (1 - g * g) := by
  unfold polePoly
  have hsq : (u + g) * (u + g) = u * u + (1 + 1 : F) * g * u + g * g := by
    calc (u + g) * (u + g)
        = (u * u + u * g) + (g * u + g * g) := by
          rw [right_distrib, CommField.left_distrib, CommField.left_distrib]
      _ = u * u + ((u * g + g * u) + g * g) := by
          rw [CommField.add_assoc (u * u), ← CommField.add_assoc (u * g)]
      _ = u * u + ((1 + 1 : F) * g * u + g * g) := by
          have h2 : u * g + g * u = (1 + 1 : F) * g * u := by
            rw [CommField.mul_comm u g, right_distrib, CommField.one_mul, right_distrib]
          rw [h2]
      _ = u * u + (1 + 1 : F) * g * u + g * g := by
          rw [← CommField.add_assoc]
  have hcancel : g * g + (1 - g * g) = 1 := by
    rw [CommField.add_comm, sub_add_cancel]
  calc u * u + (1 + 1 : F) * g * u + 1
      = (u * u + (1 + 1 : F) * g * u) + (g * g + (1 - g * g)) := by rw [hcancel]
    _ = (u * u + (1 + 1 : F) * g * u + g * g) + (1 - g * g) := by rw [← CommField.add_assoc]
    _ = (u + g) * (u + g) + (1 - g * g) := by rw [← hsq]

theorem overdamped_no_nonneg_real_root {u g : F} (hg : 0 < g) (hu : 0 ≤ u) :
    0 < polePoly u g := by
  unfold polePoly
  have h1 : 0 ≤ u * u := sq_nonneg u
  have h2 : 0 ≤ (1 + 1 : F) * g * u :=
    OrderedField.mul_nonneg (OrderedField.mul_nonneg (le_of_lt (two_pos (F := F))) (le_of_lt hg)) hu
  exact add_pos_of_nonneg_of_pos (add_nonneg h1 h2) (zero_lt_one (F := F))

theorem real_root_strictly_neg {u g : F} (hg : 0 < g) (hroot : polePoly u g = 0) :
    u < 0 := by
  rcases OrderedField.le_total 0 u with hu | hu
  · exfalso
    have hp := overdamped_no_nonneg_real_root hg hu
    rw [hroot] at hp
    exact lt_irrefl 0 hp
  · refine lt_of_le_not_le hu ?_
    intro hge0
    have heq : u = 0 := OrderedField.le_antisymm hu hge0
    rw [heq] at hroot
    unfold polePoly at hroot
    rw [mul_zero, mul_zero, CommField.zero_add, CommField.zero_add] at hroot
    exact CommField.zero_ne_one hroot.symm

theorem underdamped_no_real_roots {u g : F} (hg0 : 0 < g) (hg1 : g < 1) :
    0 < polePoly u g := by
  have hgsq : g * g < 1 := by
    have h1 : g * g < 1 * g := mul_lt_mul_of_pos_right hg1 hg0
    rw [CommField.one_mul] at h1
    exact lt_trans h1 hg1
  have hrem : 0 < 1 - g * g := sub_pos_of_lt hgsq
  rw [polePoly_complete_square]
  exact add_pos_of_nonneg_of_pos (sq_nonneg (u + g)) hrem

private theorem re_hankel_at_neg_g (g y : F) :
    (hankelDenom (⟨-g, y⟩ : C2 F) g).re = 1 - (g * g + y * y) := by
  unfold hankelDenom hankelW cAdd cMul cScale cOfReal
  dsimp
  have h1 : (-g) * (-g) = g * g := neg_mul_neg g g
  have h2 : ((1 + 1 : F) * g) * (-g) = -(g * g + g * g) := by
    rw [mul_neg, CommField.mul_assoc, right_distrib, CommField.one_mul]
  have h3 : g * g - y * y + -(g * g + g * g) = -(g * g + y * y) := by
    rw [sub_def, neg_add, CommField.add_assoc (g * g) (-(y * y)),
        CommField.add_comm (-(y * y)) (-(g * g) + -(g * g)),
        ← CommField.add_assoc (g * g) (-(g * g) + -(g * g)) (-(y * y)),
        ← CommField.add_assoc (g * g) (-(g * g)) (-(g * g)),
        CommField.add_neg_cancel, CommField.zero_add, ← neg_add]
  rw [h1, h2, h3, CommField.add_comm, ← sub_def]

theorem underdamped_complex_root_char {x y g : F} (hy : y ≠ 0) :
    hankelDenom (⟨x, y⟩ : C2 F) g = ⟨0, 0⟩ ↔ x = -g ∧ x * x + y * y = 1 := by
  constructor
  · intro h
    have him : (hankelDenom (⟨x, y⟩ : C2 F) g).im = 0 := by rw [h]
    have hre : (hankelDenom (⟨x, y⟩ : C2 F) g).re = 0 := by rw [h]
    have him_eq : (1 + 1 : F) * y * (x + g) = 0 := by
      unfold hankelDenom at him
      change (hankelW ⟨x, y⟩ g).im + 0 = 0 at him
      rw [add_zero, hankelW_im] at him
      exact him
    have h2y : (1 + 1 : F) * y ≠ 0 := by
      intro hz
      have hinv : FieldOps.inv (1 + 1 : F) * ((1 + 1 : F) * y) = 0 := by rw [hz, mul_zero]
      rw [← CommField.mul_assoc, inv_mul_cancel (ne_of_gt (two_pos (F := F))), CommField.one_mul] at hinv
      exact hy hinv
    have hxg : x + g = 0 := by
      by_cases hx0 : x + g = 0
      · exact hx0
      · exfalso
        have hnz : (1 + 1 : F) * y * (x + g) ≠ 0 := by
          intro hz
          have h1 : ((1 + 1 : F) * y * (x + g)) * FieldOps.inv (x + g) = 0 := by rw [hz, zero_mul]
          rw [CommField.mul_assoc, CommField.mul_inv_cancel (x + g) hx0, mul_one] at h1
          exact h2y h1
        exact hnz him_eq
    have hx : x = -g := by
      calc x = (x + g) - g := (add_sub_cancel x g).symm
        _ = 0 - g := by rw [hxg]
        _ = -g := zero_sub g
    rw [hx, re_hankel_at_neg_g] at hre
    have hsum1 : g * g + y * y = 1 := by
      calc g * g + y * y = (g * g + y * y) + (1 - (g * g + y * y)) := by rw [hre, add_zero]
        _ = 1 := by rw [CommField.add_comm, sub_add_cancel]
    have hnorm : x * x + y * y = 1 := by
      rw [hx, neg_mul_neg]
      exact hsum1
    exact ⟨hx, hnorm⟩
  · intro ⟨hx, hnorm⟩
    have him : (hankelDenom (⟨x, y⟩ : C2 F) g).im = 0 := by
      unfold hankelDenom
      change (hankelW ⟨x, y⟩ g).im + 0 = 0
      rw [add_zero, hankelW_im, hx, neg_add_cancel, mul_zero]
    have hre : (hankelDenom (⟨x, y⟩ : C2 F) g).re = 0 := by
      rw [hx, re_hankel_at_neg_g]
      have hsum1 : g * g + y * y = 1 := by
        rw [hx, neg_mul_neg] at hnorm
        exact hnorm
      rw [hsum1, sub_self]
    have hpair : hankelDenom (⟨x, y⟩ : C2 F) g
        = ⟨(hankelDenom (⟨x, y⟩ : C2 F) g).re, (hankelDenom (⟨x, y⟩ : C2 F) g).im⟩ := rfl
    rw [hpair, hre, him]

theorem pole_wedge_boundary_iff {pi theta mu : F}
    (hpi : 0 < pi) (hmu : 0 < mu) :
    pi ≤ (pi - theta) / mu ↔ mu ≤ 1 - theta / pi := by
  have h1 : pi ≤ (pi - theta) / mu ↔ pi * mu ≤ pi - theta := le_div_iff_of_pos hmu
  have h2 : mu ≤ 1 - theta / pi ↔ mu * pi ≤ (1 - theta / pi) * pi := by
    constructor
    · intro h; exact mul_le_mul_of_nonneg_right h (le_of_lt hpi)
    · intro h
      have hinv := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos_of_pos hpi))
      rwa [CommField.mul_assoc, CommField.mul_inv_cancel pi (ne_of_gt hpi), mul_one,
           CommField.mul_assoc, CommField.mul_inv_cancel pi (ne_of_gt hpi), mul_one] at hinv
  have hrhs : (1 - theta / pi) * pi = pi - theta := by
    rw [sub_mul, CommField.one_mul, div_mul_cancel theta (ne_of_gt hpi)]
  rw [h1, h2, hrhs, CommField.mul_comm pi mu]

theorem subdiffusive_always_pole_free {pi theta mu : F}
    (hpi : 0 < pi) (ht0 : 0 < theta) (ht1 : theta < pi / (1 + 1 : F))
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1 / (1 + 1 : F)) :
    mu < 1 - theta / pi := by
  have _ := hmu0
  have _ := ht0
  have htp : theta / pi < 1 / (1 + 1 : F) := by
    have h1 : theta < (1 / (1 + 1 : F)) * pi := by
      change theta < (1 * FieldOps.inv (1 + 1 : F)) * pi
      rw [CommField.one_mul, CommField.mul_comm]
      exact ht1
    exact (div_lt_iff_of_pos hpi).mpr h1
  have hsub : 1 - 1 / (1 + 1 : F) < 1 - theta / pi := by
    apply lt_of_sub_pos
    have heq : (1 - theta / pi) - (1 - 1 / (1 + 1 : F)) = 1 / (1 + 1 : F) - theta / pi := by
      rw [sub_def, sub_def, sub_def, neg_add, neg_neg, CommField.add_assoc,
          add_left_comm (-(theta / pi)) (-1) (1 / (1 + 1 : F)),
          ← CommField.add_assoc 1 (-1) _, CommField.add_neg_cancel, CommField.zero_add,
          CommField.add_comm, ← sub_def]
    rw [heq]
    exact sub_pos_of_lt htp
  have hhalf : (1 / (1 + 1 : F) : F) = 1 - 1 / (1 + 1 : F) := by
    have h2 : (1 + 1 : F) ≠ 0 := ne_of_gt (two_pos (F := F))
    have hsum : (1 / (1 + 1 : F) : F) + 1 / (1 + 1 : F) = 1 := by
      rw [← add_div]
      change (1 + 1 : F) * FieldOps.inv (1 + 1 : F) = 1
      exact CommField.mul_inv_cancel (1 + 1 : F) h2
    calc (1 / (1 + 1 : F) : F) = ((1 / (1 + 1 : F) : F) + 1 / (1 + 1 : F)) - 1 / (1 + 1 : F) :=
          (add_sub_cancel _ _).symm
      _ = 1 - 1 / (1 + 1 : F) := by rw [hsum]
  rw [← hhalf] at hsub
  exact lt_of_le_of_lt hmu1 hsub

end PoleBoundary

/-! ## Part IV: Abstract `PositiveLinearFunctional`, Single-Sign-Change Positivity & Geometric Sum -/

section LaplaceAndGeometric

/--
  Abstract interface for a strictly positive linear functional on an admissible linear
  subspace `Adm : (D → F) → Prop` over a domain `D` with support predicate `Supp : D → Prop`.
  Restricting `eval_pos_of_witness` to `Adm` makes atomless Lebesgue/Riemann integration
  on `C((0, ∞)) ∩ L^1((0, ∞))` a genuine model (a nonnegative continuous integrable function
  strictly positive at one point is strictly positive on an open neighborhood and thus has
  strictly positive integral), while also capturing strictly weighted finite quadrature sums
  (`Adm := fun _ => True`).
-/
structure PositiveLinearFunctional (D : Type) (F : Type) (Supp : D → Prop)
    (Adm : (D → F) → Prop) [OrderedField F] where
  adm_add : ∀ f g : D → F, Adm f → Adm g → Adm (fun r => f r + g r)
  adm_smul : ∀ (c : F) (f : D → F), Adm f → Adm (fun r => c * f r)
  eval : (D → F) → F
  eval_add : ∀ f g : D → F, Adm f → Adm g → eval (fun r => f r + g r) = eval f + eval g
  eval_smul : ∀ (c : F) (f : D → F), Adm f → eval (fun r => c * f r) = c * eval f
  eval_nonneg : ∀ f : D → F, Adm f → (∀ r, Supp r → 0 ≤ f r) → 0 ≤ eval f
  eval_pos_of_witness :
    ∀ f : D → F, Adm f → (∀ r, Supp r → 0 ≤ f r) → (∃ r, Supp r ∧ 0 < f r) → 0 < eval f

/--
  **Single-Sign-Change Laplace Positivity Theorem**:
  If `phi` and `phi * k` lie in the admissible subspace `Adm` (e.g., `C((0, ∞)) ∩ L^1((0, ∞))`),
  `∫ φ = 0`, `φ ≥ 0` and `k(r) ≥ k(r0)` on `(0, r0]`, `φ ≤ 0` and `k(r) ≤ k(r0)` on `[r0, ∞)`,
  and there is at least one strict point `r_* ∈ Supp` where `φ(r_*) * (k(r_*) - k(r0)) > 0`,
  then `∫ φ(r) k(r) dr > 0`.
  Applied with `φ(r) = r K_{μ,g}(r)` and `k(r) = e^{-rt}`, this proves `-Ġ_{μ,g}(t) > 0`
  for all `t > 0` across the entire pole-free wedge (`g ≥ 1`, or `g < 1, μ ∈ (1/2, μ_pole(g))`).
-/
theorem single_sign_change_integral_pos
    {D F : Type} {Supp : D → Prop} {Adm : (D → F) → Prop} [OrderedField F]
    (L : PositiveLinearFunctional D F Supp Adm)
    (phi k : D → F) (r0 : D)
    (hphi_adm : Adm phi)
    (hprod_adm : Adm (fun r => phi r * k r))
    (hzero : L.eval phi = 0)
    (halign : ∀ r, Supp r → (0 ≤ phi r ∧ k r0 ≤ k r) ∨ (phi r ≤ 0 ∧ k r ≤ k r0))
    (hwitness : ∃ r_star, Supp r_star ∧
      ((0 < phi r_star ∧ k r0 < k r_star) ∨ (phi r_star < 0 ∧ k r_star < k r0))) :
    0 < L.eval (fun r => phi r * k r) := by
  let g : D → F := fun r => phi r * (k r - k r0)
  have hg_eq : g = (fun r => phi r * k r + (-k r0) * phi r) := by
    funext r
    dsimp [g]
    rw [mul_sub, sub_def, neg_mul, CommField.mul_comm (phi r) (k r0)]
  have hg_adm : Adm g := by
    rw [hg_eq]
    exact L.adm_add _ _ hprod_adm (L.adm_smul (-k r0) phi hphi_adm)
  have hscaled_adm : Adm (fun r => k r0 * phi r) := L.adm_smul (k r0) phi hphi_adm
  have hdecomp : (fun r => phi r * k r) = (fun r => g r + k r0 * phi r) := by
    funext r
    dsimp [g]
    rw [mul_sub, CommField.mul_comm (k r0) (phi r), sub_add_cancel]
  have heval : L.eval (fun r => phi r * k r) = L.eval g := by
    rw [hdecomp, L.eval_add g (fun r => k r0 * phi r) hg_adm hscaled_adm,
        L.eval_smul (k r0) phi hphi_adm, hzero, mul_zero, add_zero]
  rw [heval]
  refine L.eval_pos_of_witness g hg_adm ?_ ?_
  · intro r hr
    rcases halign r hr with ⟨hp, hk⟩ | ⟨hp, hk⟩
    · exact OrderedField.mul_nonneg hp (sub_nonneg_of_le hk)
    · have hkd : k r - k r0 ≤ 0 := nonpos_of_neg_nonneg (by
        rw [sub_def, neg_add, neg_neg, CommField.add_comm, ← sub_def]
        exact sub_nonneg_of_le hk)
      exact mul_nonneg_of_nonpos_of_nonpos hp hkd
  · rcases hwitness with ⟨r_star, hrs, ⟨hp, hk⟩ | ⟨hp, hk⟩⟩
    · exact ⟨r_star, hrs, OrderedField.mul_pos hp (sub_pos_of_lt hk)⟩
    · have hkd : k r_star - k r0 < 0 := neg_of_neg_pos (by
        rw [sub_def, neg_add, neg_neg, CommField.add_comm, ← sub_def]
        exact sub_pos_of_lt hk)
      exact ⟨r_star, hrs, mul_pos_of_neg_of_neg hp hkd⟩

/-! ### Concrete Weighted-Sum Instantiation (Satisfiability of `PositiveLinearFunctional`) -/

def finSum {F : Type} [CommField F] : {n : Nat} → (Fin n → F) → F
  | 0, _ => 0
  | n + 1, f => finSum (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem finSum_add {F : Type} [CommField F] :
    ∀ {n : Nat} (f g : Fin n → F), finSum (fun i => f i + g i) = finSum f + finSum g
  | 0, _, _ => (add_zero (0 : F)).symm
  | n + 1, f, g => by
      dsimp [finSum]
      rw [finSum_add (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                     (fun i : Fin n => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
      rw [CommField.add_assoc, add_left_comm (finSum (fun i : Fin n => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)),
          ← CommField.add_assoc]

theorem finSum_smul {F : Type} [CommField F] :
    ∀ {n : Nat} (c : F) (f : Fin n → F), finSum (fun i => c * f i) = c * finSum f
  | 0, c, _ => (mul_zero c).symm
  | n + 1, c, f => by
      dsimp [finSum]
      rw [finSum_smul c (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩), ← CommField.left_distrib]

theorem finSum_nonneg {F : Type} [OrderedField F] :
    ∀ {n : Nat} (f : Fin n → F), (∀ i, 0 ≤ f i) → 0 ≤ finSum f
  | 0, _, _ => OrderedField.le_refl 0
  | n + 1, f, hf => by
      dsimp [finSum]
      exact add_nonneg
        (finSum_nonneg (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (fun i => hf _))
        (hf ⟨n, Nat.lt_succ_self n⟩)

theorem finSum_pos_of_witness {F : Type} [OrderedField F] :
    ∀ {n : Nat} (f : Fin n → F), (∀ i, 0 ≤ f i) → (∃ i, 0 < f i) → 0 < finSum f
  | 0, _, _, ⟨i, _⟩ => Fin.elim0 i
  | n + 1, f, hf, ⟨i, hi⟩ => by
      dsimp [finSum]
      by_cases hlast : i.val = n
      · have heq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hlast
        rw [heq] at hi
        exact add_pos_of_nonneg_of_pos
          (finSum_nonneg (fun j : Fin n => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) (fun j => hf _))
          hi
      · have hlt : i.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hlast
        have hsum_pos : 0 < finSum (fun j : Fin n => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) :=
          finSum_pos_of_witness _ (fun j => hf _) ⟨⟨i.val, hlt⟩, hi⟩
        exact add_pos_of_pos_of_nonneg hsum_pos (hf ⟨n, Nat.lt_succ_self n⟩)

def weightedSumFunctional {F : Type} [OrderedField F] {n : Nat}
    (w : Fin n → F) (hw : ∀ i, 0 < w i) :
    PositiveLinearFunctional (Fin n) F (fun _ => True) (fun _ => True) where
  adm_add := fun _ _ _ _ => trivial
  adm_smul := fun _ _ _ => trivial
  eval := fun f => finSum (fun i => w i * f i)
  eval_add := fun f g _ _ => by
    dsimp
    have heq : (fun i => w i * (f i + g i)) = (fun i => w i * f i + w i * g i) := by
      funext i; exact CommField.left_distrib (w i) (f i) (g i)
    rw [heq, finSum_add]
  eval_smul := fun c f _ => by
    dsimp
    have heq : (fun i => w i * (c * f i)) = (fun i => c * (w i * f i)) := by
      funext i; exact mul_left_comm (w i) c (f i)
    rw [heq, finSum_smul]
  eval_nonneg := fun f _ hf =>
    finSum_nonneg _ (fun i => OrderedField.mul_nonneg (le_of_lt (hw i)) (hf i trivial))
  eval_pos_of_witness := fun f _ hf ⟨i, _, hi⟩ =>
    finSum_pos_of_witness _ (fun j => OrderedField.mul_nonneg (le_of_lt (hw j)) (hf j trivial))
      ⟨i, OrderedField.mul_pos (hw i) hi⟩

/-! ### Exact `μ = 1` Geometric Series Partial Sums & Tail Convergence Bound -/

def powF {F : Type} [CommField F] (q : F) : Nat → F
  | 0 => 1
  | n + 1 => powF q n * q

def geomPartialSum {F : Type} [CommField F] (q : F) : Nat → F
  | 0 => 0
  | n + 1 => geomPartialSum q n + powF q (n + 1)

theorem ofNatF_nonneg {F : Type} [OrderedField F] : ∀ n : Nat, (0 : F) ≤ ofNatF n
  | 0 => OrderedField.le_refl 0
  | n + 1 => add_nonneg (ofNatF_nonneg n) (le_of_lt (zero_lt_one (F := F)))

theorem powF_pos {F : Type} [OrderedField F] {q : F} (hq : 0 < q) :
    ∀ n : Nat, 0 < powF q n
  | 0 => zero_lt_one (F := F)
  | n + 1 => OrderedField.mul_pos (powF_pos hq n) hq

theorem powF_mul_inv {F : Type} [CommField F] {q : F} (hq : q ≠ 0) :
    ∀ n : Nat, powF (FieldOps.inv q) n * powF q n = 1
  | 0 => CommField.one_mul 1
  | n + 1 => by
      dsimp [powF]
      calc (powF (FieldOps.inv q) n * FieldOps.inv q) * (powF q n * q)
          = (powF (FieldOps.inv q) n * powF q n) * (FieldOps.inv q * q) := by
              rw [CommField.mul_assoc, mul_left_comm (FieldOps.inv q) (powF q n) q, ← CommField.mul_assoc]
        _ = 1 * 1 := by rw [powF_mul_inv hq n, inv_mul_cancel hq]
        _ = 1 := CommField.one_mul 1

/--
  Exact algebraic identity for partial sums of the `μ = 1` BLP geometric revival series:
  `(1 - q) * ∑_{k=1}^N q^k = q * (1 - q^N)`.
-/
theorem geom_partial_sum_identity {F : Type} [CommField F] (q : F) :
    ∀ N : Nat, (1 - q) * geomPartialSum q N = q * (1 - powF q N)
  | 0 => by
      dsimp [geomPartialSum, powF]
      rw [mul_zero, sub_self, mul_zero]
  | n + 1 => by
      dsimp [geomPartialSum, powF]
      rw [CommField.left_distrib, geom_partial_sum_identity q n]
      have hterm : (1 - q) * (powF q n * q) = q * powF q n - q * (powF q n * q) := by
        rw [sub_mul, CommField.one_mul]
        exact congrArg (fun z => z - q * (powF q n * q)) (CommField.mul_comm (powF q n) q)
      rw [hterm, mul_sub, mul_sub, mul_one, sub_def, sub_def, sub_def,
          CommField.add_assoc, ← CommField.add_assoc (-(q * powF q n)) (q * powF q n),
          neg_add_cancel, CommField.zero_add]

theorem bernoulli_ineq {F : Type} [OrderedField F] {d : F} (hd : 0 ≤ d) :
    ∀ n : Nat, 1 + ofNatF n * d ≤ powF (1 + d) n
  | 0 => by
      dsimp [ofNatF, powF]
      rw [zero_mul, add_zero]
      exact OrderedField.le_refl 1
  | n + 1 => by
      dsimp [ofNatF, powF]
      have ih := bernoulli_ineq hd n
      have h1d : 0 ≤ 1 + d := add_nonneg (le_of_lt (zero_lt_one (F := F))) hd
      have hmul : (1 + ofNatF n * d) * (1 + d) ≤ powF (1 + d) n * (1 + d) :=
        mul_le_mul_of_nonneg_right ih h1d
      have hexp : (1 + ofNatF n * d) * (1 + d)
          = 1 + (ofNatF n + 1) * d + (ofNatF n * d) * d := by
        calc (1 + ofNatF n * d) * (1 + d)
            = (1 + d) + (ofNatF n * d + (ofNatF n * d) * d) := by
              rw [right_distrib, CommField.one_mul, CommField.left_distrib, mul_one]
          _ = 1 + (ofNatF n * d + d) + (ofNatF n * d) * d := by
              rw [← CommField.add_assoc (1 + d), CommField.add_assoc 1 d (ofNatF n * d),
                  CommField.add_comm d (ofNatF n * d), ← CommField.add_assoc 1 (ofNatF n * d) d]
          _ = 1 + (ofNatF n + 1) * d + (ofNatF n * d) * d := by
              rw [right_distrib, CommField.one_mul]
      have hdrop : 1 + (ofNatF n + 1) * d ≤ (1 + ofNatF n * d) * (1 + d) := by
        rw [hexp]
        have hdd : 0 ≤ (ofNatF n * d) * d :=
          OrderedField.mul_nonneg (OrderedField.mul_nonneg (ofNatF_nonneg n) hd) hd
        have hle := OrderedField.add_le_add_left (1 + (ofNatF n + 1) * d) hdd
        rwa [add_zero] at hle
      exact OrderedField.le_trans hdrop hmul

/--
  Archimedean remainder bound for `N_BLP(1, g) = ∑_{k=1}^∞ q^k = q / (1 - q)` (`q = e^{-πg/√(1-g^2)} ∈ (0, 1)`):
  setting `d = q^{-1} - 1 > 0`, `0 < q/(1-q) - ∑_{k=1}^N q^k ≤ (q/(1-q)) / (1 + N d)`.
-/
theorem geom_tail_archimedean_bound {F : Type} [OrderedField F]
    {q : F} (hq0 : 0 < q) (hq1 : q < 1) (N : Nat) :
    let d := FieldOps.inv q - 1
    0 < d ∧
    0 < q / (1 - q) - geomPartialSum q N ∧
    q / (1 - q) - geomPartialSum q N ≤ (q / (1 - q)) / (1 + ofNatF N * d) := by
  intro d
  have h1mq : 0 < 1 - q := sub_pos_of_lt hq1
  have h1mq_ne : 1 - q ≠ 0 := ne_of_gt h1mq
  have hinv_gt1 : 1 < FieldOps.inv q := by
    have hmul : q * 1 < q * FieldOps.inv q := by
      rw [mul_one, CommField.mul_inv_cancel q (ne_of_gt hq0)]
      exact hq1
    rcases OrderedField.le_total (FieldOps.inv q) 1 with hle | hlt
    · exfalso
      have h2 := mul_le_mul_of_nonneg_left hle (le_of_lt hq0)
      exact not_le_of_lt hmul h2
    · exact lt_of_le_not_le hlt (fun hle => not_le_of_lt hmul (mul_le_mul_of_nonneg_left hle (le_of_lt hq0)))
  have hd_pos : 0 < d := sub_pos_of_lt hinv_gt1
  have h1d : 1 + d = FieldOps.inv q := by
    dsimp [d]
    rw [CommField.add_comm, sub_add_cancel]
  have hbern : 1 + ofNatF N * d ≤ powF (FieldOps.inv q) N := by
    rw [← h1d]
    exact bernoulli_ineq (le_of_lt hd_pos) N
  have hden_pos : 0 < 1 + ofNatF N * d :=
    add_pos_of_pos_of_nonneg (zero_lt_one (F := F)) (OrderedField.mul_nonneg (ofNatF_nonneg N) (le_of_lt hd_pos))
  have hqn_pos : 0 < powF q N := powF_pos hq0 N
  have hdiff_eq : q / (1 - q) - geomPartialSum q N = (q / (1 - q)) * powF q N := by
    have hsum : geomPartialSum q N = (q * (1 - powF q N)) / (1 - q) := by
      rw [← geom_partial_sum_identity q N]
      symm
      change ((1 - q) * geomPartialSum q N) * FieldOps.inv (1 - q) = geomPartialSum q N
      rw [CommField.mul_comm (1 - q) (geomPartialSum q N), CommField.mul_assoc,
          CommField.mul_inv_cancel (1 - q) h1mq_ne, mul_one]
    rw [hsum]
    change q * FieldOps.inv (1 - q) - (q * (1 - powF q N)) * FieldOps.inv (1 - q)
         = (q * FieldOps.inv (1 - q)) * powF q N
    rw [← sub_mul]
    have hnum : q - q * (1 - powF q N) = q * powF q N := by
      rw [mul_sub, mul_one, sub_def, sub_def, neg_add, neg_neg,
          ← CommField.add_assoc, CommField.add_neg_cancel, CommField.zero_add]
    rw [hnum, mul_right_comm q (powF q N) (FieldOps.inv (1 - q))]
  have hdiff_pos : 0 < q / (1 - q) - geomPartialSum q N := by
    rw [hdiff_eq]
    exact OrderedField.mul_pos (div_pos hq0 h1mq) hqn_pos
  have hqn_le : powF q N ≤ FieldOps.inv (1 + ofNatF N * d) := by
    have hmul : (1 + ofNatF N * d) * powF q N ≤ powF (FieldOps.inv q) N * powF q N :=
      mul_le_mul_of_nonneg_right hbern (le_of_lt hqn_pos)
    rw [powF_mul_inv (ne_of_gt hq0)] at hmul
    rw [CommField.mul_comm] at hmul
    rw [← CommField.one_mul (FieldOps.inv (1 + ofNatF N * d))]
    change powF q N ≤ 1 / (1 + ofNatF N * d)
    exact (le_div_iff_of_pos hden_pos).mpr hmul
  have hbound : q / (1 - q) - geomPartialSum q N ≤ (q / (1 - q)) / (1 + ofNatF N * d) := by
    rw [hdiff_eq]
    change (q / (1 - q)) * powF q N ≤ (q / (1 - q)) * FieldOps.inv (1 + ofNatF N * d)
    exact mul_le_mul_of_nonneg_left hqn_le (le_of_lt (div_pos hq0 h1mq))
  exact ⟨hd_pos, hdiff_pos, hbound⟩

end LaplaceAndGeometric

/-! ## Part V: 4x4 Choi Matrices, Fujiwara-Algoet Theorem, Pauli Subordination & 6-Level Hierarchy -/

section ChoiAndHierarchy

structure V4 (α : Type) where
  v0 : α
  v1 : α
  v2 : α
  v3 : α

structure M4 (α : Type) where
  r0 : V4 α
  r1 : V4 α
  r2 : V4 α
  r3 : V4 α

section General4x4

variable {F : Type} [CommField F]

def dotV4C2 (u v : V4 (C2 F)) : C2 F :=
  cAdd (cAdd (cMul (cConj u.v0) v.v0) (cMul (cConj u.v1) v.v1))
       (cAdd (cMul (cConj u.v2) v.v2) (cMul (cConj u.v3) v.v3))

def rowDotC2 (r v : V4 (C2 F)) : C2 F :=
  cAdd (cAdd (cMul r.v0 v.v0) (cMul r.v1 v.v1))
       (cAdd (cMul r.v2 v.v2) (cMul r.v3 v.v3))

def mulM4V4C2 (A : M4 (C2 F)) (v : V4 (C2 F)) : V4 (C2 F) :=
  ⟨rowDotC2 A.r0 v, rowDotC2 A.r1 v, rowDotC2 A.r2 v, rowDotC2 A.r3 v⟩

def quadForm4 (A : M4 (C2 F)) (v : V4 (C2 F)) : F :=
  (dotV4C2 v (mulM4V4C2 A v)).re

def ofRealV4 (x : V4 F) : V4 (C2 F) :=
  ⟨cOfReal x.v0, cOfReal x.v1, cOfReal x.v2, cOfReal x.v3⟩

def ofRealM4 (A : M4 F) : M4 (C2 F) :=
  ⟨ofRealV4 A.r0, ofRealV4 A.r1, ofRealV4 A.r2, ofRealV4 A.r3⟩

def realDotV4 (u v : V4 F) : F :=
  u.v0 * v.v0 + u.v1 * v.v1 + u.v2 * v.v2 + u.v3 * v.v3

def mulM4V4R (A : M4 F) (v : V4 F) : V4 F :=
  ⟨realDotV4 A.r0 v, realDotV4 A.r1 v, realDotV4 A.r2 v, realDotV4 A.r3 v⟩

def realQuad4 (A : M4 F) (v : V4 F) : F :=
  realDotV4 v (mulM4V4R A v)

def m4AddR (A B : M4 F) : M4 F :=
  let vAdd := fun (a b : V4 F) => ⟨a.v0 + b.v0, a.v1 + b.v1, a.v2 + b.v2, a.v3 + b.v3⟩
  ⟨vAdd A.r0 B.r0, vAdd A.r1 B.r1, vAdd A.r2 B.r2, vAdd A.r3 B.r3⟩

def rank1Mat (d : F) (u : V4 F) : M4 F :=
  let row := fun (ui : F) => ⟨d * (ui * u.v0), d * (ui * u.v1), d * (ui * u.v2), d * (ui * u.v3)⟩
  ⟨row u.v0, row u.v1, row u.v2, row u.v3⟩

theorem realQuad4_rank1 (d : F) (u x : V4 F) :
    realQuad4 (rank1Mat d u) x = d * (realDotV4 u x * realDotV4 u x) := by
  let S := realDotV4 u x
  have hrow : ∀ ui : F,
      (d * (ui * u.v0)) * x.v0 + (d * (ui * u.v1)) * x.v1
        + (d * (ui * u.v2)) * x.v2 + (d * (ui * u.v3)) * x.v3
      = d * (ui * S) := by
    intro ui
    have term : ∀ uj xj : F, (d * (ui * uj)) * xj = d * (ui * (uj * xj)) := by
      intro uj xj
      rw [CommField.mul_assoc d (ui * uj) xj, CommField.mul_assoc ui uj xj]
    rw [term u.v0 x.v0, term u.v1 x.v1, term u.v2 x.v2, term u.v3 x.v3]
    rw [← CommField.left_distrib, ← CommField.left_distrib, ← CommField.left_distrib,
        ← CommField.left_distrib, ← CommField.left_distrib, ← CommField.left_distrib]
    rfl
  unfold realQuad4 mulM4V4R realDotV4 rank1Mat
  dsimp
  rw [hrow u.v0, hrow u.v1, hrow u.v2, hrow u.v3]
  have swap : ∀ xi ui : F, xi * (d * (ui * S)) = (d * S) * (ui * xi) := by
    intro xi ui
    calc xi * (d * (ui * S))
        = (d * (ui * S)) * xi := CommField.mul_comm _ _
      _ = d * ((ui * S) * xi) := CommField.mul_assoc _ _ _
      _ = d * (S * (ui * xi)) := by
          rw [mul_right_comm ui S xi, CommField.mul_comm (ui * xi) S]
      _ = (d * S) * (ui * xi) := (CommField.mul_assoc d S (ui * xi)).symm
  rw [swap x.v0 u.v0, swap x.v1 u.v1, swap x.v2 u.v2, swap x.v3 u.v3]
  rw [← CommField.left_distrib, ← CommField.left_distrib, ← CommField.left_distrib]
  exact CommField.mul_assoc d S S

theorem realDotV4_add (u v w : V4 F) :
    realDotV4 u ⟨v.v0 + w.v0, v.v1 + w.v1, v.v2 + w.v2, v.v3 + w.v3⟩
      = realDotV4 u v + realDotV4 u w := by
  unfold realDotV4
  dsimp
  rw [CommField.left_distrib, CommField.left_distrib, CommField.left_distrib, CommField.left_distrib]
  -- Group first terms and second terms cleanly
  calc (u.v0 * v.v0 + u.v0 * w.v0) + (u.v1 * v.v1 + u.v1 * w.v1)
        + (u.v2 * v.v2 + u.v2 * w.v2) + (u.v3 * v.v3 + u.v3 * w.v3)
      = ((u.v0 * v.v0 + u.v1 * v.v1) + (u.v0 * w.v0 + u.v1 * w.v1))
        + ((u.v2 * v.v2 + u.v3 * v.v3) + (u.v2 * w.v2 + u.v3 * w.v3)) := by
          have p1 : (u.v0 * v.v0 + u.v0 * w.v0) + (u.v1 * v.v1 + u.v1 * w.v1)
              = (u.v0 * v.v0 + u.v1 * v.v1) + (u.v0 * w.v0 + u.v1 * w.v1) := by
            rw [CommField.add_assoc, add_left_comm (u.v0 * w.v0) (u.v1 * v.v1), ← CommField.add_assoc]
          have p2 : (u.v2 * v.v2 + u.v2 * w.v2) + (u.v3 * v.v3 + u.v3 * w.v3)
              = (u.v2 * v.v2 + u.v3 * v.v3) + (u.v2 * w.v2 + u.v3 * w.v3) := by
            rw [CommField.add_assoc, add_left_comm (u.v2 * w.v2) (u.v3 * v.v3), ← CommField.add_assoc]
          rw [CommField.add_assoc ((u.v0 * v.v0 + u.v0 * w.v0) + (u.v1 * v.v1 + u.v1 * w.v1)),
              p1, p2]
    _ = ((u.v0 * v.v0 + u.v1 * v.v1) + (u.v2 * v.v2 + u.v3 * v.v3))
        + ((u.v0 * w.v0 + u.v1 * w.v1) + (u.v2 * w.v2 + u.v3 * w.v3)) := by
          rw [CommField.add_assoc, add_left_comm (u.v0 * w.v0 + u.v1 * w.v1) (u.v2 * v.v2 + u.v3 * v.v3),
              ← CommField.add_assoc]
    _ = (u.v0 * v.v0 + u.v1 * v.v1 + u.v2 * v.v2 + u.v3 * v.v3)
        + (u.v0 * w.v0 + u.v1 * w.v1 + u.v2 * w.v2 + u.v3 * w.v3) := by
          rw [← CommField.add_assoc (u.v0 * v.v0 + u.v1 * v.v1) (u.v2 * v.v2),
              ← CommField.add_assoc (u.v0 * w.v0 + u.v1 * w.v1) (u.v2 * w.v2)]

theorem realQuad4_add (A B : M4 F) (x : V4 F) :
    realQuad4 (m4AddR A B) x = realQuad4 A x + realQuad4 B x := by
  unfold realQuad4 mulM4V4R m4AddR
  dsimp
  have radd : ∀ r1 r2 : V4 F,
      realDotV4 ⟨r1.v0 + r2.v0, r1.v1 + r2.v1, r1.v2 + r2.v2, r1.v3 + r2.v3⟩ x
      = realDotV4 r1 x + realDotV4 r2 x := by
    intro r1 r2
    unfold realDotV4
    dsimp
    rw [right_distrib, right_distrib, right_distrib, right_distrib]
    have p1 : (r1.v0 * x.v0 + r2.v0 * x.v0) + (r1.v1 * x.v1 + r2.v1 * x.v1)
        = (r1.v0 * x.v0 + r1.v1 * x.v1) + (r2.v0 * x.v0 + r2.v1 * x.v1) := by
      rw [CommField.add_assoc, add_left_comm (r2.v0 * x.v0) (r1.v1 * x.v1), ← CommField.add_assoc]
    have p2 : (r1.v2 * x.v2 + r2.v2 * x.v2) + (r1.v3 * x.v3 + r2.v3 * x.v3)
        = (r1.v2 * x.v2 + r1.v3 * x.v3) + (r2.v2 * x.v2 + r2.v3 * x.v3) := by
      rw [CommField.add_assoc, add_left_comm (r2.v2 * x.v2) (r1.v3 * x.v3), ← CommField.add_assoc]
    calc ((r1.v0 * x.v0 + r2.v0 * x.v0) + (r1.v1 * x.v1 + r2.v1 * x.v1)
           + (r1.v2 * x.v2 + r2.v2 * x.v2)) + (r1.v3 * x.v3 + r2.v3 * x.v3)
        = ((r1.v0 * x.v0 + r2.v0 * x.v0) + (r1.v1 * x.v1 + r2.v1 * x.v1))
           + ((r1.v2 * x.v2 + r2.v2 * x.v2) + (r1.v3 * x.v3 + r2.v3 * x.v3)) := by
            rw [CommField.add_assoc]
      _ = ((r1.v0 * x.v0 + r1.v1 * x.v1) + (r2.v0 * x.v0 + r2.v1 * x.v1))
           + ((r1.v2 * x.v2 + r1.v3 * x.v3) + (r2.v2 * x.v2 + r2.v3 * x.v3)) := by
            rw [p1, p2]
      _ = ((r1.v0 * x.v0 + r1.v1 * x.v1) + (r1.v2 * x.v2 + r1.v3 * x.v3))
           + ((r2.v0 * x.v0 + r2.v1 * x.v1) + (r2.v2 * x.v2 + r2.v3 * x.v3)) := by
            rw [CommField.add_assoc, add_left_comm (r2.v0 * x.v0 + r2.v1 * x.v1), ← CommField.add_assoc]
      _ = (r1.v0 * x.v0 + r1.v1 * x.v1 + r1.v2 * x.v2 + r1.v3 * x.v3)
           + (r2.v0 * x.v0 + r2.v1 * x.v1 + r2.v2 * x.v2 + r2.v3 * x.v3) := by
            rw [← CommField.add_assoc (r1.v0 * x.v0 + r1.v1 * x.v1),
                ← CommField.add_assoc (r2.v0 * x.v0 + r2.v1 * x.v1)]
  rw [radd A.r0 B.r0, radd A.r1 B.r1, radd A.r2 B.r2, radd A.r3 B.r3]
  exact realDotV4_add x (mulM4V4R A x) (mulM4V4R B x)

def v4Re (v : V4 (C2 F)) : V4 F := ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
def v4Im (v : V4 (C2 F)) : V4 F := ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩

private theorem c2_real_rowDot (r : V4 F) (v : V4 (C2 F)) :
    rowDotC2 (ofRealV4 r) v = ⟨realDotV4 r (v4Re v), realDotV4 r (v4Im v)⟩ := by
  unfold rowDotC2 ofRealV4 realDotV4 v4Re v4Im cAdd cMul cOfReal
  dsimp
  simp only [zero_mul, sub_zero, add_zero, CommField.zero_add]
  congr 1 <;> rw [← CommField.add_assoc]

private theorem c2_conj_mul_re (u w : C2 F) :
    (cMul (cConj u) w).re = u.re * w.re + u.im * w.im := by
  unfold cMul cConj
  dsimp
  rw [neg_mul, sub_def, neg_neg]

theorem quadForm4_ofRealM4 (A : M4 F) (v : V4 (C2 F)) :
    quadForm4 (ofRealM4 A) v = realQuad4 A (v4Re v) + realQuad4 A (v4Im v) := by
  unfold quadForm4 mulM4V4C2 ofRealM4
  dsimp
  rw [c2_real_rowDot A.r0 v, c2_real_rowDot A.r1 v, c2_real_rowDot A.r2 v, c2_real_rowDot A.r3 v]
  unfold dotV4C2 cAdd
  dsimp
  rw [c2_conj_mul_re, c2_conj_mul_re, c2_conj_mul_re, c2_conj_mul_re]
  unfold v4Re v4Im realQuad4 mulM4V4R realDotV4
  dsimp
  have p1 : (v.v0.re * realDotV4 A.r0 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
             + v.v0.im * realDotV4 A.r0 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)
          + (v.v1.re * realDotV4 A.r1 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
             + v.v1.im * realDotV4 A.r1 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)
      = (v.v0.re * realDotV4 A.r0 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v1.re * realDotV4 A.r1 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩)
      + (v.v0.im * realDotV4 A.r0 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
         + v.v1.im * realDotV4 A.r1 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩) := by
    rw [CommField.add_assoc, add_left_comm (v.v0.im * _) (v.v1.re * _), ← CommField.add_assoc]
  have p2 : (v.v2.re * realDotV4 A.r2 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
             + v.v2.im * realDotV4 A.r2 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)
          + (v.v3.re * realDotV4 A.r3 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
             + v.v3.im * realDotV4 A.r3 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)
      = (v.v2.re * realDotV4 A.r2 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v3.re * realDotV4 A.r3 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩)
      + (v.v2.im * realDotV4 A.r2 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
         + v.v3.im * realDotV4 A.r3 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩) := by
    rw [CommField.add_assoc, add_left_comm (v.v2.im * _) (v.v3.re * _), ← CommField.add_assoc]
  calc ((v.v0.re * realDotV4 A.r0 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v0.im * realDotV4 A.r0 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)
        + (v.v1.re * realDotV4 A.r1 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v1.im * realDotV4 A.r1 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩))
       + ((v.v2.re * realDotV4 A.r2 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v2.im * realDotV4 A.r2 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)
        + (v.v3.re * realDotV4 A.r3 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v3.im * realDotV4 A.r3 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩))
      = ((v.v0.re * realDotV4 A.r0 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
          + v.v1.re * realDotV4 A.r1 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩)
         + (v.v0.im * realDotV4 A.r0 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
          + v.v1.im * realDotV4 A.r1 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩))
        + ((v.v2.re * realDotV4 A.r2 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
          + v.v3.re * realDotV4 A.r3 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩)
         + (v.v2.im * realDotV4 A.r2 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
          + v.v3.im * realDotV4 A.r3 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)) := by rw [p1, p2]
    _ = ((v.v0.re * realDotV4 A.r0 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
          + v.v1.re * realDotV4 A.r1 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩)
         + (v.v2.re * realDotV4 A.r2 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
          + v.v3.re * realDotV4 A.r3 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩))
        + ((v.v0.im * realDotV4 A.r0 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
          + v.v1.im * realDotV4 A.r1 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)
         + (v.v2.im * realDotV4 A.r2 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
          + v.v3.im * realDotV4 A.r3 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩)) := by
          rw [CommField.add_assoc, add_left_comm (v.v0.im * _ + v.v1.im * _) (v.v2.re * _ + v.v3.re * _),
              ← CommField.add_assoc]
    _ = (v.v0.re * realDotV4 A.r0 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v1.re * realDotV4 A.r1 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v2.re * realDotV4 A.r2 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩
         + v.v3.re * realDotV4 A.r3 ⟨v.v0.re, v.v1.re, v.v2.re, v.v3.re⟩)
        + (v.v0.im * realDotV4 A.r0 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
         + v.v1.im * realDotV4 A.r1 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
         + v.v2.im * realDotV4 A.r2 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩
         + v.v3.im * realDotV4 A.r3 ⟨v.v0.im, v.v1.im, v.v2.im, v.v3.im⟩) := by
          rw [← CommField.add_assoc (v.v0.re * _ + v.v1.re * _),
              ← CommField.add_assoc (v.v0.im * _ + v.v1.im * _)]

end General4x4

section Ordered4x4

variable {F : Type} [OrderedField F]

def isPSD4 (A : M4 (C2 F)) : Prop := ∀ v : V4 (C2 F), 0 ≤ quadForm4 A v

def ldlt4Mat (d0 d1 d2 d3 l10 l20 l30 l21 l31 l32 : F) : M4 F :=
  m4AddR (rank1Mat d0 ⟨1, l10, l20, l30⟩)
    (m4AddR (rank1Mat d1 ⟨0, 1, l21, l31⟩)
      (m4AddR (rank1Mat d2 ⟨0, 0, 1, l32⟩) (rank1Mat d3 ⟨0, 0, 0, 1⟩)))

theorem ldlt4_isPSD {d0 d1 d2 d3 l10 l20 l30 l21 l31 l32 : F}
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) :
    isPSD4 (ofRealM4 (ldlt4Mat d0 d1 d2 d3 l10 l20 l30 l21 l31 l32)) := by
  intro v
  rw [quadForm4_ofRealM4]
  have hreal : ∀ x : V4 F, 0 ≤ realQuad4 (ldlt4Mat d0 d1 d2 d3 l10 l20 l30 l21 l31 l32) x := by
    intro x
    unfold ldlt4Mat
    rw [realQuad4_add, realQuad4_add, realQuad4_add,
        realQuad4_rank1, realQuad4_rank1, realQuad4_rank1, realQuad4_rank1]
    exact add_nonneg
      (OrderedField.mul_nonneg hd0 (sq_nonneg _))
      (add_nonneg (OrderedField.mul_nonneg hd1 (sq_nonneg _))
        (add_nonneg (OrderedField.mul_nonneg hd2 (sq_nonneg _))
          (OrderedField.mul_nonneg hd3 (sq_nonneg _))))
  exact add_nonneg (hreal (v4Re v)) (hreal (v4Im v))

/-! ### Pauli Channel Choi Matrix & Fujiwara–Algoet Bell Diagonalization -/

private theorem two_mul_eq {F : Type} [CommField F] (x : F) : (1 + 1 : F) * x = x + x := by
  rw [right_distrib, CommField.one_mul]

private theorem add4_mid {F : Type} [CommField F] (p q r s : F) :
    (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [CommField.add_assoc p q (r + s), add_left_comm q r s, ← CommField.add_assoc p r (q + s)]

private theorem add4_swap {F : Type} [CommField F] (p q r s : F) :
    (p + q) + (r + s) = (p + s) + (q + r) := by
  rw [CommField.add_comm r s, add4_mid]

private theorem sq_add_pair {F : Type} [CommField F] (x y : F) :
    (x + y) * (x + y) = (x * x + y * y) + (1 + 1 : F) * (x * y) := by
  calc (x + y) * (x + y)
      = (x * x + x * y) + (y * x + y * y) := by
          rw [right_distrib, CommField.left_distrib, CommField.left_distrib]
    _ = (x * x + y * y) + (x * y + y * x) := add4_swap _ _ _ _
    _ = (x * x + y * y) + (1 + 1 : F) * (x * y) := by rw [CommField.mul_comm y x, two_mul_eq]

private theorem sq_sub_pair {F : Type} [CommField F] (x y : F) :
    (x - y) * (x - y) = (x * x + y * y) - (1 + 1 : F) * (x * y) := by
  have h := sq_add_pair x (-y)
  change (x + -y) * (x + -y) = (x * x + (-y) * (-y)) + (1 + 1 : F) * (x * (-y)) at h
  rw [neg_mul_neg, mul_neg, mul_neg, ← sub_def, ← sub_def] at h
  exact h

private theorem real_pair_bell_scaled {F : Type} [CommField F] (a b x y : F) :
    (1 + 1 : F) * (a * (x * x) + b * (x * y) + (b * (y * x) + a * (y * y)))
      = (a + b) * ((x + y) * (x + y)) + (a - b) * ((x - y) * (x - y)) := by
  let P := x * x + y * y
  let Q := (1 + 1 : F) * (x * y)
  have hL : a * (x * x) + b * (x * y) + (b * (y * x) + a * (y * y)) = a * P + b * Q := by
    calc a * (x * x) + b * (x * y) + (b * (y * x) + a * (y * y))
        = (a * (x * x) + a * (y * y)) + (b * (x * y) + b * (y * x)) := add4_swap _ _ _ _
      _ = a * (x * x + y * y) + b * (x * y + y * x) := by
          rw [← CommField.left_distrib, ← CommField.left_distrib]
      _ = a * P + b * Q := by rw [CommField.mul_comm y x, ← two_mul_eq (x * y)]
  have hR : (a + b) * ((x + y) * (x + y)) + (a - b) * ((x - y) * (x - y))
      = (1 + 1 : F) * (a * P + b * Q) := by
    rw [sq_add_pair, sq_sub_pair]
    change (a + b) * (P + Q) + (a - b) * (P - Q) = (1 + 1 : F) * (a * P + b * Q)
    have h1 : (a + b) * (P + Q) = (a * P + a * Q) + (b * P + b * Q) := by
      rw [right_distrib, CommField.left_distrib a P Q, CommField.left_distrib b P Q]
    have h2 : (a - b) * (P - Q) = (a * P - a * Q) - (b * P - b * Q) := by
      rw [sub_mul, mul_sub, mul_sub]
    have h2' : (a * P - a * Q) - (b * P - b * Q) = (a * P + -(a * Q)) + (-(b * P) + b * Q) := by
      rw [sub_def, sub_def, sub_def, neg_add, neg_neg]
    rw [h1, h2, h2']
    calc ((a * P + a * Q) + (b * P + b * Q)) + ((a * P + -(a * Q)) + (-(b * P) + b * Q))
        = ((a * P + a * Q) + (a * P + -(a * Q))) + ((b * P + b * Q) + (-(b * P) + b * Q)) :=
            add4_mid _ _ _ _
      _ = ((a * P + a * P) + (a * Q + -(a * Q))) + ((b * P + -(b * P)) + (b * Q + b * Q)) := by
            rw [add4_mid (a * P) (a * Q) (a * P) (-(a * Q)),
                add4_mid (b * P) (b * Q) (-(b * P)) (b * Q)]
      _ = (a * P + a * P) + (b * Q + b * Q) := by
            rw [CommField.add_neg_cancel, add_zero, CommField.add_neg_cancel, CommField.zero_add]
      _ = (1 + 1 : F) * (a * P + b * Q) := by
            rw [← two_mul_eq (a * P), ← two_mul_eq (b * Q), ← CommField.left_distrib]
  rw [hL, hR]

private theorem real_pair_bell (a b x y : F) :
    a * (x * x) + b * (x * y) + (b * (y * x) + a * (y * y))
      = ((a + b) * ((x + y) * (x + y)) + (a - b) * ((x - y) * (x - y))) / (1 + 1 : F) := by
  have h2 : (1 + 1 : F) ≠ 0 := ne_of_gt (two_pos (F := F))
  rw [← real_pair_bell_scaled a b x y]
  change _ = ((1 + 1 : F) * _) * FieldOps.inv (1 + 1 : F)
  rw [CommField.mul_comm (1 + 1 : F), CommField.mul_assoc,
      CommField.mul_inv_cancel (1 + 1 : F) h2, mul_one]

def choiPauliReal (rx ry rz : F) : M4 F :=
  let four := ofNatF (F := F) 4
  let a := (1 + rz) / four
  let b := (rx + ry) / four
  let c := (1 - rz) / four
  let d := (rx - ry) / four
  ⟨⟨a, 0, 0, b⟩, ⟨0, c, d, 0⟩, ⟨0, d, c, 0⟩, ⟨b, 0, 0, a⟩⟩

def choiPauliMat (rx ry rz : F) : M4 (C2 F) :=
  ofRealM4 (choiPauliReal rx ry rz)

private theorem realQuad4_pauliReal (rx ry rz : F) (x : V4 F) :
    realQuad4 (choiPauliReal rx ry rz) x =
      (((1 + rz) / ofNatF 4 + (rx + ry) / ofNatF 4) * ((x.v0 + x.v3) * (x.v0 + x.v3))
       + ((1 + rz) / ofNatF 4 - (rx + ry) / ofNatF 4) * ((x.v0 - x.v3) * (x.v0 - x.v3))
       + ((1 - rz) / ofNatF 4 + (rx - ry) / ofNatF 4) * ((x.v1 + x.v2) * (x.v1 + x.v2))
       + ((1 - rz) / ofNatF 4 - (rx - ry) / ofNatF 4) * ((x.v1 - x.v2) * (x.v1 - x.v2))) / (1 + 1 : F) := by
  unfold realQuad4 mulM4V4R realDotV4 choiPauliReal
  dsimp
  simp only [zero_mul, CommField.zero_add, add_zero]
  have h03 :
      x.v0 * ((1 + rz) / ofNatF 4 * x.v0 + (rx + ry) / ofNatF 4 * x.v3)
      + x.v3 * ((rx + ry) / ofNatF 4 * x.v0 + (1 + rz) / ofNatF 4 * x.v3)
      = ((1 + rz) / ofNatF 4 * (x.v0 * x.v0) + (rx + ry) / ofNatF 4 * (x.v0 * x.v3))
        + ((rx + ry) / ofNatF 4 * (x.v3 * x.v0) + (1 + rz) / ofNatF 4 * (x.v3 * x.v3)) := by
    rw [CommField.left_distrib, CommField.left_distrib,
        mul_left_comm x.v0 ((1 + rz) / ofNatF 4) x.v0,
        mul_left_comm x.v0 ((rx + ry) / ofNatF 4) x.v3,
        mul_left_comm x.v3 ((rx + ry) / ofNatF 4) x.v0,
        mul_left_comm x.v3 ((1 + rz) / ofNatF 4) x.v3]
  have h12 :
      x.v1 * ((1 - rz) / ofNatF 4 * x.v1 + (rx - ry) / ofNatF 4 * x.v2)
      + x.v2 * ((rx - ry) / ofNatF 4 * x.v1 + (1 - rz) / ofNatF 4 * x.v2)
      = ((1 - rz) / ofNatF 4 * (x.v1 * x.v1) + (rx - ry) / ofNatF 4 * (x.v1 * x.v2))
        + ((rx - ry) / ofNatF 4 * (x.v2 * x.v1) + (1 - rz) / ofNatF 4 * (x.v2 * x.v2)) := by
    rw [CommField.left_distrib, CommField.left_distrib,
        mul_left_comm x.v1 ((1 - rz) / ofNatF 4) x.v1,
        mul_left_comm x.v1 ((rx - ry) / ofNatF 4) x.v2,
        mul_left_comm x.v2 ((rx - ry) / ofNatF 4) x.v1,
        mul_left_comm x.v2 ((1 - rz) / ofNatF 4) x.v2]
  have hgrp : ∀ p0 p1 p2 p3 : F, ((p0 + p1) + p2) + p3 = (p0 + p3) + (p1 + p2) := by
    intro p0 p1 p2 p3
    rw [CommField.add_assoc (p0 + p1) p2 p3, add4_swap p0 p1 p2 p3]
  rw [hgrp, h03, h12,
      real_pair_bell ((1 + rz) / ofNatF 4) ((rx + ry) / ofNatF 4) x.v0 x.v3,
      real_pair_bell ((1 - rz) / ofNatF 4) ((rx - ry) / ofNatF 4) x.v1 x.v2,
      ← add_div, ← CommField.add_assoc]

private theorem ofNatF_4_eq_four_ones : ofNatF (F := F) 4 = (1 + 1 + 1 + 1 : F) := by
  dsimp [ofNatF]
  rw [CommField.zero_add]

private theorem ofNatF_4_pos : (0 : F) < ofNatF 4 := by
  rw [ofNatF_4_eq_four_ones]
  exact add_pos (add_pos (add_pos (zero_lt_one (F := F)) (zero_lt_one (F := F))) (zero_lt_one (F := F))) (zero_lt_one (F := F))

private theorem ofNatF_4_eq : (ofNatF (F := F) 4) ≠ 0 :=
  ne_of_gt ofNatF_4_pos

private theorem ofNatF_4_mul_2 : ofNatF (F := F) 4 * (1 + 1 : F) = ofNatF (F := F) 8 := by
  rw [ofNatF_4_eq_four_ones]
  dsimp [ofNatF]
  rw [CommField.zero_add, CommField.left_distrib, mul_one,
      ← CommField.add_assoc, ← CommField.add_assoc, ← CommField.add_assoc]

private theorem div_four_add_div_four (u v : F) : u / ofNatF 4 + v / ofNatF 4 = (u + v) / ofNatF 4 :=
  (add_div u v (ofNatF 4)).symm

private theorem div_four_sub_div_four (u v : F) : u / ofNatF 4 - v / ofNatF 4 = (u - v) / ofNatF 4 :=
  (sub_div u v (ofNatF 4)).symm

private theorem div_four_div_two (u : F) : (u / ofNatF 4) / (1 + 1 : F) = u / ofNatF 8 := by
  change (u * FieldOps.inv (ofNatF 4)) * FieldOps.inv (1 + 1 : F) = u * FieldOps.inv (ofNatF 8)
  rw [CommField.mul_assoc]
  congr 1
  have h4 : (ofNatF (F := F) 4) ≠ 0 := ofNatF_4_eq
  have h2 : (1 + 1 : F) ≠ 0 := ne_of_gt (two_pos (F := F))
  have h8 : (ofNatF (F := F) 8) ≠ 0 := by
    rw [← ofNatF_4_mul_2]
    exact ne_of_gt (OrderedField.mul_pos ofNatF_4_pos (two_pos (F := F)))
  have hprod : (FieldOps.inv (ofNatF 4) * FieldOps.inv (1 + 1 : F)) * ofNatF 8 = 1 := by
    rw [← ofNatF_4_mul_2, CommField.mul_assoc,
        mul_left_comm (FieldOps.inv (1 + 1 : F)) (ofNatF 4) (1 + 1 : F),
        inv_mul_cancel h2, mul_one, inv_mul_cancel h4]
  calc FieldOps.inv (ofNatF 4) * FieldOps.inv (1 + 1 : F)
      = (FieldOps.inv (ofNatF 4) * FieldOps.inv (1 + 1 : F)) * (ofNatF 8 * FieldOps.inv (ofNatF 8)) := by
          rw [CommField.mul_inv_cancel _ h8, mul_one]
    _ = ((FieldOps.inv (ofNatF 4) * FieldOps.inv (1 + 1 : F)) * ofNatF 8) * FieldOps.inv (ofNatF 8) :=
          (CommField.mul_assoc _ _ _).symm
    _ = FieldOps.inv (ofNatF 8) := by rw [hprod, CommField.one_mul]

/--
  **Fujiwara–Algoet Bell Diagonalization Theorem** for the `4×4` Pauli Choi matrix over any `OrderedField F`:
  `v† J_Pauli(rx, ry, rz) v = [(1+rx+ry+rz)|v0+v3|² + (1-rx-ry+rz)|v0-v3|² + (1+rx-ry-rz)|v1+v2|² + (1-rx+ry-rz)|v1-v2|²] / 8`.
-/
theorem pauli_choi_fujiwara_algoet (rx ry rz : F) (v : V4 (C2 F)) :
    quadForm4 (choiPauliMat rx ry rz) v =
      ((1 + rx + ry + rz) * cNormSq (cAdd v.v0 v.v3)
       + (1 - rx - ry + rz) * cNormSq (cSub v.v0 v.v3)
       + (1 + rx - ry - rz) * cNormSq (cAdd v.v1 v.v2)
       + (1 - rx + ry - rz) * cNormSq (cSub v.v1 v.v2)) / ofNatF 8 := by
  unfold choiPauliMat
  rw [quadForm4_ofRealM4, realQuad4_pauliReal, realQuad4_pauliReal, ← add_div]
  have e0 : (1 + rz) / ofNatF 4 + (rx + ry) / ofNatF 4 = (1 + rx + ry + rz) / ofNatF 4 := by
    rw [div_four_add_div_four]; congr 1
    rw [CommField.add_comm 1 rz, CommField.add_assoc rz 1 (rx + ry),
        CommField.add_comm rz (1 + (rx + ry)), ← CommField.add_assoc 1 rx ry]
  have ez : (1 + rz) / ofNatF 4 - (rx + ry) / ofNatF 4 = (1 - rx - ry + rz) / ofNatF 4 := by
    rw [div_four_sub_div_four]; congr 1
    rw [sub_def, sub_def, sub_def, neg_add, CommField.add_comm 1 rz,
        CommField.add_assoc rz 1 (-rx + -ry), CommField.add_comm rz (1 + (-rx + -ry)),
        ← CommField.add_assoc 1 (-rx) (-ry)]
  have ex : (1 - rz) / ofNatF 4 + (rx - ry) / ofNatF 4 = (1 + rx - ry - rz) / ofNatF 4 := by
    rw [div_four_add_div_four]; congr 1
    rw [sub_def, sub_def, sub_def, sub_def, CommField.add_comm 1 (-rz),
        CommField.add_assoc (-rz) 1 (rx + -ry), CommField.add_comm (-rz) (1 + (rx + -ry)),
        ← CommField.add_assoc 1 rx (-ry)]
  have ey : (1 - rz) / ofNatF 4 - (rx - ry) / ofNatF 4 = (1 - rx + ry - rz) / ofNatF 4 := by
    rw [div_four_sub_div_four]; congr 1
    rw [sub_def, sub_def, sub_def, sub_def, neg_add, neg_neg, CommField.add_comm 1 (-rz),
        CommField.add_assoc (-rz) 1 (-rx + ry), CommField.add_comm (-rz) (1 + (-rx + ry)),
        ← CommField.add_assoc 1 (-rx) ry, ← sub_def 1 rx]
  rw [e0, ez, ex, ey]
  dsimp [v4Re, v4Im, cNormSq, cAdd, cSub]
  let l0 := (1 + rx + ry + rz) / ofNatF 4
  let lz := (1 - rx - ry + rz) / ofNatF 4
  let lx := (1 + rx - ry - rz) / ofNatF 4
  let ly := (1 - rx + ry - rz) / ofNatF 4
  let n0r := (v.v0.re + v.v3.re) * (v.v0.re + v.v3.re)
  let n0i := (v.v0.im + v.v3.im) * (v.v0.im + v.v3.im)
  let nzr := (v.v0.re - v.v3.re) * (v.v0.re - v.v3.re)
  let nzi := (v.v0.im - v.v3.im) * (v.v0.im - v.v3.im)
  let nxr := (v.v1.re + v.v2.re) * (v.v1.re + v.v2.re)
  let nxi := (v.v1.im + v.v2.im) * (v.v1.im + v.v2.im)
  let nyr := (v.v1.re - v.v2.re) * (v.v1.re - v.v2.re)
  let nyi := (v.v1.im - v.v2.im) * (v.v1.im - v.v2.im)
  have hsum :
      ((l0 * n0r + lz * nzr + lx * nxr + ly * nyr)
       + (l0 * n0i + lz * nzi + lx * nxi + ly * nyi))
      = ((1 + rx + ry + rz) * (n0r + n0i)
         + (1 - rx - ry + rz) * (nzr + nzi)
         + (1 + rx - ry - rz) * (nxr + nxi)
         + (1 - rx + ry - rz) * (nyr + nyi)) / ofNatF 4 := by
    have p1 : (l0 * n0r + lz * nzr) + (l0 * n0i + lz * nzi)
        = (l0 * (n0r + n0i)) + (lz * (nzr + nzi)) := by
      rw [add4_mid, ← CommField.left_distrib, ← CommField.left_distrib]
    have p2 : (lx * nxr + ly * nyr) + (lx * nxi + ly * nyi)
        = (lx * (nxr + nxi)) + (ly * (nyr + nyi)) := by
      rw [add4_mid, ← CommField.left_distrib, ← CommField.left_distrib]
    calc ((l0 * n0r + lz * nzr + lx * nxr + ly * nyr)
           + (l0 * n0i + lz * nzi + lx * nxi + ly * nyi))
        = (((l0 * n0r + lz * nzr) + (lx * nxr + ly * nyr))
           + ((l0 * n0i + lz * nzi) + (lx * nxi + ly * nyi))) := by
            rw [CommField.add_assoc (l0 * n0r + lz * nzr) (lx * nxr) (ly * nyr),
                CommField.add_assoc (l0 * n0i + lz * nzi) (lx * nxi) (ly * nyi)]
      _ = ((l0 * n0r + lz * nzr) + (l0 * n0i + lz * nzi))
           + ((lx * nxr + ly * nyr) + (lx * nxi + ly * nyi)) := add4_mid _ _ _ _
      _ = (l0 * (n0r + n0i) + lz * (nzr + nzi)) + (lx * (nxr + nxi) + ly * (nyr + nyi)) := by
            rw [p1, p2]
      _ = (l0 * (n0r + n0i) + lz * (nzr + nzi) + lx * (nxr + nxi) + ly * (nyr + nyi)) := by
            rw [← CommField.add_assoc]
      _ = ((1 + rx + ry + rz) * (n0r + n0i)
           + (1 - rx - ry + rz) * (nzr + nzi)
           + (1 + rx - ry - rz) * (nxr + nxi)
           + (1 - rx + ry - rz) * (nyr + nyi)) / ofNatF 4 := by
            have mpull : ∀ u k : F, (u / ofNatF 4) * k = (u * k) / ofNatF 4 := by
              intro u k
              change (u * FieldOps.inv (ofNatF 4)) * k = (u * k) * FieldOps.inv (ofNatF 4)
              rw [mul_right_comm]
            dsimp [l0, lz, lx, ly]
            rw [mpull, mpull, mpull, mpull,
                div_four_add_div_four, div_four_add_div_four, div_four_add_div_four]
  rw [hsum, div_four_div_two]

theorem pauli_choi_psd_of_eigs {rx ry rz : F}
    (h0 : 0 ≤ 1 + rx + ry + rz)
    (hz : 0 ≤ 1 - rx - ry + rz)
    (hx : 0 ≤ 1 + rx - ry - rz)
    (hy : 0 ≤ 1 - rx + ry - rz) :
    isPSD4 (choiPauliMat rx ry rz) := by
  intro v
  rw [pauli_choi_fujiwara_algoet]
  have h8 : (0 : F) < ofNatF 8 := by
    rw [← ofNatF_4_mul_2]
    exact OrderedField.mul_pos ofNatF_4_pos (two_pos (F := F))
  refine div_nonneg ?_ h8
  have nc : ∀ a : C2 F, 0 ≤ cNormSq a := fun a => add_nonneg (sq_nonneg a.re) (sq_nonneg a.im)
  exact add_nonneg
    (add_nonneg
      (add_nonneg (OrderedField.mul_nonneg h0 (nc _)) (OrderedField.mul_nonneg hz (nc _)))
      (OrderedField.mul_nonneg hx (nc _)))
    (OrderedField.mul_nonneg hy (nc _))

private theorem cNormSq_zero_pair : cNormSq (⟨0, 0⟩ : C2 F) = 0 := by
  unfold cNormSq; dsimp; rw [mul_zero, add_zero]

theorem pauli_choi_witness_z (rx ry rz : F) :
    quadForm4 (choiPauliMat rx ry rz) ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩⟩
      = (1 - rx - ry + rz) / (1 + 1 : F) := by
  rw [pauli_choi_fujiwara_algoet]
  have hc0 : cAdd (⟨1, 0⟩ : C2 F) ⟨-1, 0⟩ = ⟨0, 0⟩ := by
    unfold cAdd; dsimp; rw [CommField.add_neg_cancel, add_zero]
  have hc1 : cAdd (⟨0, 0⟩ : C2 F) ⟨0, 0⟩ = ⟨0, 0⟩ := by
    unfold cAdd; dsimp; rw [add_zero]
  have hc2 : cSub (⟨0, 0⟩ : C2 F) ⟨0, 0⟩ = ⟨0, 0⟩ := by
    unfold cSub; dsimp; rw [sub_self]
  have hcz : cNormSq (cSub (⟨1, 0⟩ : C2 F) ⟨-1, 0⟩) = ofNatF 4 := by
    unfold cNormSq cSub
    dsimp [cNormSq, cSub]
    rw [sub_def, neg_neg, sub_self, mul_zero, add_zero, ofNatF_4_eq_four_ones,
        CommField.left_distrib, mul_one, ← CommField.add_assoc]
  rw [hc0, hc1, hc2, cNormSq_zero_pair, hcz]
  simp only [mul_zero, CommField.zero_add, add_zero]
  rw [← ofNatF_4_mul_2, CommField.mul_comm (ofNatF 4) (1 + 1 : F)]
  change ((1 - rx - ry + rz) * ofNatF 4) * FieldOps.inv ((1 + 1 : F) * ofNatF 4) = _
  have h2 : (1 + 1 : F) ≠ 0 := ne_of_gt (two_pos (F := F))
  have h24 : (1 + 1 : F) * ofNatF 4 ≠ 0 := ne_of_gt (OrderedField.mul_pos (two_pos (F := F)) ofNatF_4_pos)
  have hmul : ((1 - rx - ry + rz) / (1 + 1 : F)) * ((1 + 1 : F) * ofNatF 4) = (1 - rx - ry + rz) * ofNatF 4 := by
    rw [← CommField.mul_assoc, div_mul_cancel _ h2]
  rw [← hmul]
  change (((1 - rx - ry + rz) / (1 + 1 : F)) * ((1 + 1 : F) * ofNatF 4)) * FieldOps.inv ((1 + 1 : F) * ofNatF 4) = _
  rw [CommField.mul_assoc, CommField.mul_inv_cancel _ h24, mul_one]

theorem pauli_choi_witness_x (rx ry rz : F) :
    quadForm4 (choiPauliMat rx ry rz) ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩
      = (1 + rx - ry - rz) / (1 + 1 : F) := by
  rw [pauli_choi_fujiwara_algoet]
  have hc0 : cAdd (⟨0, 0⟩ : C2 F) ⟨0, 0⟩ = ⟨0, 0⟩ := by unfold cAdd; dsimp; rw [add_zero]
  have hcz : cSub (⟨0, 0⟩ : C2 F) ⟨0, 0⟩ = ⟨0, 0⟩ := by unfold cSub; dsimp; rw [sub_self]
  have hcy : cSub (⟨1, 0⟩ : C2 F) ⟨1, 0⟩ = ⟨0, 0⟩ := by unfold cSub; dsimp; rw [sub_self, sub_self]
  have hcx : cNormSq (cAdd (⟨1, 0⟩ : C2 F) ⟨1, 0⟩) = ofNatF 4 := by
    unfold cNormSq cAdd
    dsimp [cNormSq, cAdd]
    rw [add_zero, mul_zero, add_zero, ofNatF_4_eq_four_ones,
        CommField.left_distrib, mul_one, ← CommField.add_assoc]
  rw [hc0, hcz, hcy, cNormSq_zero_pair, hcx]
  simp only [mul_zero, CommField.zero_add, add_zero]
  rw [← ofNatF_4_mul_2, CommField.mul_comm (ofNatF 4) (1 + 1 : F)]
  have h2 : (1 + 1 : F) ≠ 0 := ne_of_gt (two_pos (F := F))
  have h24 : (1 + 1 : F) * ofNatF 4 ≠ 0 := ne_of_gt (OrderedField.mul_pos (two_pos (F := F)) ofNatF_4_pos)
  have hmul : ((1 + rx - ry - rz) / (1 + 1 : F)) * ((1 + 1 : F) * ofNatF 4) = (1 + rx - ry - rz) * ofNatF 4 := by
    rw [← CommField.mul_assoc, div_mul_cancel _ h2]
  rw [← hmul]
  change (((1 + rx - ry - rz) / (1 + 1 : F)) * ((1 + 1 : F) * ofNatF 4)) * FieldOps.inv ((1 + 1 : F) * ofNatF 4) = _
  rw [CommField.mul_assoc, CommField.mul_inv_cancel _ h24, mul_one]

/-! ### Pauli Semigroup Subordination CP-Divisibility Criterion & Counterexample -/

theorem pauli_subordination_cp_sufficient
    (kappa : F → F)
    (hmono : ∀ a b : F, 0 ≤ a → a ≤ b → kappa a ≤ kappa b)
    (hsub : ∀ a b : F, 0 ≤ a → 0 ≤ b → kappa (a + b) ≤ kappa a + kappa b)
    {gx gy gz : F} (hgx : 0 ≤ gx) (hgy : 0 ≤ gy) (hgz : 0 ≤ gz) :
    let lx := gy + gz
    let ly := gx + gz
    let lz := gx + gy
    0 ≤ (kappa ly + kappa lz - kappa lx) / (1 + 1 : F) ∧
    0 ≤ (kappa lx + kappa lz - kappa ly) / (1 + 1 : F) ∧
    0 ≤ (kappa lx + kappa ly - kappa lz) / (1 + 1 : F) := by
  intro lx ly lz
  have htri : ∀ a b c : F, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      0 ≤ (kappa (a + c) + kappa (a + b) - kappa (b + c)) / (1 + 1 : F) := by
    intro a b c ha hb hc
    have hle : b + c ≤ (a + c) + (a + b) := by
      have h2a : 0 ≤ a + a := add_nonneg ha ha
      have heq : (a + c) + (a + b) = (b + c) + (a + a) := by
        rw [add4_mid, CommField.add_comm c b, CommField.add_comm (a + a) (b + c)]
      rw [heq]
      have h0 := OrderedField.add_le_add_left (b + c) h2a
      rwa [add_zero] at h0
    have hk : kappa (b + c) ≤ kappa (a + c) + kappa (a + b) :=
      OrderedField.le_trans (hmono _ _ (add_nonneg hb hc) hle)
        (hsub _ _ (add_nonneg ha hc) (add_nonneg ha hb))
    exact div_nonneg (sub_nonneg_of_le hk) (two_pos (F := F))
  dsimp [lx, ly, lz]
  refine ⟨htri gx gy gz hgx hgy hgz, ?_, ?_⟩
  · have h := htri gy gx gz hgy hgx hgz
    rwa [CommField.add_comm gy gx] at h
  · have h := htri gz gx gy hgz hgx hgy
    rwa [CommField.add_comm gz gy, CommField.add_comm gz gx] at h

theorem pauli_subordination_cp_broken
    (kappa : F → F) {lx ly lz : F}
    (hviol : kappa ly + kappa lz < kappa lx) :
    (kappa ly + kappa lz - kappa lx) / (1 + 1 : F) < 0 := by
  have hnum : kappa ly + kappa lz - kappa lx < 0 := by
    have hp := sub_pos_of_lt hviol
    have hn := neg_lt_zero_of_pos hp
    have heq : -(kappa lx - (kappa ly + kappa lz)) = kappa ly + kappa lz - kappa lx := by
      rw [sub_def, neg_add, neg_neg, CommField.add_comm, ← sub_def]
    rwa [heq] at hn
  change (kappa ly + kappa lz - kappa lx) * FieldOps.inv (1 + 1 : F) < 0
  exact mul_neg_of_neg_of_pos hnum (inv_pos_of_pos (two_pos (F := F)))

/--
  Concrete finite-step Pauli-subordination counterexample witness (`μ = 0.95`, `(γ_x, γ_y, γ_z) = (48, 2, 2)`,
  step `[1.0, 1.1]` where `r_x ≈ 0.812505 ≤ 813/1000` and `r_y = r_z ≈ 0.910311 ≥ 910/1000`):
  every Bloch axis strictly contracts (`0 < r_k < 1`), yet the intermediate Choi matrix has
  strictly negative eigenvalue (`quadForm4 < 0` on the Bell vector `(0, 1, 1, 0)`).
-/
theorem pauli_subord_mu095_counterexample
    {rx ry : Q}
    (hrx0 : (0 : Q) < rx) (hrx1 : rx ≤ mkQ 813 1000)
    (hry0 : mkQ 910 1000 ≤ ry) (hry1 : ry < (1 : Q)) :
    (0 < rx ∧ rx < 1) ∧
    (0 < ry ∧ ry < 1) ∧
    quadForm4 (choiPauliMat rx ry ry) ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩ < 0 := by
  have h813lt1 : mkQ 813 1000 < 1 := mkQ_lt_of (by decide)
  have h0lt910 : (0 : Q) < mkQ 910 1000 := mkQ_lt_of (by decide)
  refine ⟨⟨hrx0, lt_of_le_of_lt hrx1 h813lt1⟩, ⟨lt_of_lt_of_le h0lt910 hry0, hry1⟩, ?_⟩
  rw [pauli_choi_witness_x]
  have hsum : (1 + rx) - ry - ry ≤ (1 + mkQ 813 1000) - mkQ 910 1000 - mkQ 910 1000 := by
    have h1 : 1 + rx ≤ 1 + mkQ 813 1000 := OrderedField.add_le_add_left 1 hrx1
    have h2 : -ry ≤ -(mkQ 910 1000) := by
      have hp := sub_nonneg_of_le hry0
      rw [sub_def, CommField.add_comm] at hp
      exact le_of_sub_nonneg (by rwa [sub_def, neg_neg])
    exact add_le_add (add_le_add h1 h2) h2
  have hneg_bnd : (1 + mkQ 813 1000) - mkQ 910 1000 - mkQ 910 1000 < (0 : Q) := by
    apply mkQ_lt_of; decide
  have hnum_neg : 1 + rx - ry - ry < 0 := lt_of_le_of_lt hsum hneg_bnd
  change (1 + rx - ry - ry) * FieldOps.inv (1 + 1 : Q) < 0
  exact mul_neg_of_neg_of_pos hnum_neg (inv_pos_of_pos (two_pos (F := Q)))

/-! ### Non-Unital Channel Choi Positivity (`LDLT`) & BKM vs. Euclidean Separation -/

def choiNonUnitalReal (a b c mx mz : F) : M4 F :=
  let four := ofNatF (F := F) 4
  let s00 := (1 + mz + c) / four
  let s01 := (mx + b) / four
  let s03 := ((1 + 1 : F) * a) / four
  let s11 := (1 - mz - c) / four
  let s22 := (1 + mz - c) / four
  let s23 := (mx - b) / four
  let s33 := (1 - mz + c) / four
  ⟨⟨s00, s01, 0, s03⟩,
   ⟨s01, s11, 0, 0⟩,
   ⟨0, 0, s22, s23⟩,
   ⟨s03, 0, s23, s33⟩⟩

def choiNonUnitalMat (a b c mx mz : F) : M4 (C2 F) :=
  ofRealM4 (choiNonUnitalReal a b c mx mz)

def euclidShearForm (kxx kxz kzz vx vy vz : F) : F :=
  (1 + 1 : F) * (kxx * (vx * vx) + kxx * (vy * vy) + kzz * (vz * vz) + kxz * (vx * vz))

def bkmShearDecayForm (kxx kxz kzz gxx gzz vx vy vz : F) : F :=
  let a := (1 + 1 : F) * (-kxx) * gxx
  let b := -gxx * kxz
  let c := (1 + 1 : F) * (-kzz) * gzz
  a * (vx * vx) + (1 + 1 : F) * b * (vx * vz) + c * (vz * vz) + a * (vy * vy)

/--
  Sylvester quadratic positivity theorem:
  if `a > 0`, `a * c - b^2 > 0`, and `d > 0`, then
  `a x^2 + 2 b x z + c z^2 + d y^2 > 0` for every nonzero `(x, y, z)`.
-/
theorem sylvester_quad3_pos {a b c d x y z : F}
    (ha : 0 < a) (hdet : 0 < a * c - b * b) (hd : 0 < d)
    (hnz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < a * (x * x) + (1 + 1 : F) * b * (x * z) + c * (z * z) + d * (y * y) := by
  let w := x + (b / a) * z
  have hcomplete :
      a * (x * x) + (1 + 1 : F) * b * (x * z) + c * (z * z)
      = a * (w * w) + ((a * c - b * b) / a) * (z * z) := by
    have hne : a ≠ 0 := ne_of_gt ha
    have hwsq : a * (w * w) = a * (x * x) + (1 + 1 : F) * b * (x * z) + ((b * b) / a) * (z * z) := by
      dsimp [w]
      rw [sq_add_pair x ((b / a) * z), CommField.left_distrib, CommField.left_distrib]
      have t2 : a * ((1 + 1 : F) * (x * ((b / a) * z))) = (1 + 1 : F) * b * (x * z) := by
        calc a * ((1 + 1 : F) * (x * ((b / a) * z)))
            = (1 + 1 : F) * (x * ((a * (b / a)) * z)) := by
              rw [mul_left_comm a (1 + 1 : F), mul_left_comm a x, CommField.mul_assoc a (b / a) z]
          _ = (1 + 1 : F) * (x * (b * z)) := by
              rw [CommField.mul_comm a (b / a), div_mul_cancel b hne]
          _ = (1 + 1 : F) * b * (x * z) := by
              rw [mul_left_comm x b z, ← CommField.mul_assoc]
      have t3 : a * (((b / a) * z) * ((b / a) * z)) = ((b * b) / a) * (z * z) := by
        calc a * (((b / a) * z) * ((b / a) * z))
            = a * (((b / a) * (b / a)) * (z * z)) := by
              rw [← CommField.mul_assoc ((b / a) * z) (b / a) z,
                  mul_right_comm (b / a) z (b / a),
                  CommField.mul_assoc ((b / a) * (b / a)) z z]
          _ = ((a * (b / a)) * (b / a)) * (z * z) := by
              rw [← CommField.mul_assoc a ((b / a) * (b / a)) (z * z),
                  ← CommField.mul_assoc a (b / a) (b / a)]
          _ = ((b * b) / a) * (z * z) := by
              rw [CommField.mul_comm a (b / a), div_mul_cancel b hne]
              change (b * (b * FieldOps.inv a)) * (z * z) = ((b * b) * FieldOps.inv a) * (z * z)
              rw [← CommField.mul_assoc b b (FieldOps.inv a)]
      rw [t2, t3, CommField.add_assoc (a * (x * x)), CommField.add_comm (((b * b) / a) * (z * z)),
          ← CommField.add_assoc]
    have hrem : ((b * b) / a) * (z * z) + ((a * c - b * b) / a) * (z * z) = c * (z * z) := by
      rw [← right_distrib, ← add_div, sub_def, CommField.add_comm (a * c) (-(b * b)),
          ← CommField.add_assoc (b * b) (-(b * b)) (a * c),
          CommField.add_neg_cancel, CommField.zero_add]
      have hdiv : (a * c) / a = c := by
        change (a * c) * FieldOps.inv a = c
        rw [CommField.mul_comm a c, CommField.mul_assoc, CommField.mul_inv_cancel a hne, mul_one]
      rw [hdiv]
    rw [hwsq, CommField.add_assoc (a * (x * x) + (1 + 1 : F) * b * (x * z)), hrem]
  have hsum :
      a * (x * x) + (1 + 1 : F) * b * (x * z) + c * (z * z) + d * (y * y)
      = a * (w * w) + ((a * c - b * b) / a) * (z * z) + d * (y * y) := by
    rw [hcomplete]
  rw [hsum]
  have t1_nn : 0 ≤ a * (w * w) := OrderedField.mul_nonneg (le_of_lt ha) (sq_nonneg w)
  have hdet_div : 0 < (a * c - b * b) / a := div_pos hdet ha
  have t2_nn : 0 ≤ ((a * c - b * b) / a) * (z * z) :=
    OrderedField.mul_nonneg (le_of_lt hdet_div) (sq_nonneg z)
  have t3_nn : 0 ≤ d * (y * y) := OrderedField.mul_nonneg (le_of_lt hd) (sq_nonneg y)
  rcases hnz with hx | hy | hz
  · by_cases hz0 : z = 0
    · have hw : w = x := by
        dsimp [w]
        rw [hz0, mul_zero, add_zero]
      have hw_nz : w ≠ 0 := by rwa [hw]
      have t1_pos : 0 < a * (w * w) := OrderedField.mul_pos ha (sq_pos_of_ne_zero hw_nz)
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg t1_pos t2_nn) t3_nn
    · have t2_pos : 0 < ((a * c - b * b) / a) * (z * z) :=
        OrderedField.mul_pos hdet_div (sq_pos_of_ne_zero hz0)
      exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos t1_nn t2_pos) t3_nn
  · have t3_pos : 0 < d * (y * y) := OrderedField.mul_pos hd (sq_pos_of_ne_zero hy)
    exact add_pos_of_nonneg_of_pos (add_nonneg t1_nn t2_nn) t3_pos
  · have t2_pos : 0 < ((a * c - b * b) / a) * (z * z) :=
      OrderedField.mul_pos hdet_div (sq_pos_of_ne_zero hz)
    exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos t1_nn t2_pos) t3_nn

/-! ### Formal 6-Level Hierarchy Separations over `Q` -/

private theorem v4_ext {α : Type} {a b : V4 α}
    (h0 : a.v0 = b.v0) (h1 : a.v1 = b.v1) (h2 : a.v2 = b.v2) (h3 : a.v3 = b.v3) : a = b := by
  cases a; cases b; subst h0; subst h1; subst h2; subst h3; rfl

private theorem m4_ext {α : Type} {a b : M4 α}
    (h0 : a.r0 = b.r0) (h1 : a.r1 = b.r1) (h2 : a.r2 = b.r2) (h3 : a.r3 = b.r3) : a = b := by
  cases a; cases b; subst h0; subst h1; subst h2; subst h3; rfl

theorem q_inv_mkQ_pos {n : Int} {d : Nat} (hn : 0 < n) (hd : 0 < d) :
    FieldOps.inv (mkQ n d hd) = mkQ (d : Int) n.natAbs (Int.natAbs_pos.mpr (Int.ne_of_gt hn)) := by
  change Quotient.mk qSetoid (qInvRaw ⟨n, d, hd⟩) = Quotient.mk qSetoid _
  apply Quotient.sound
  show qEq (qInvRaw ⟨n, d, hd⟩) _
  unfold qInvRaw
  rw [dif_pos hn]
  rfl

theorem q_ofNatF_4 : ofNatF (F := Q) 4 = mkQ 4 1 := by
  apply mkQ_eq_of; decide

-- 1. `Semigroup ⊊ CM`: convex mixture `c(t) = (2^{-t} + 4^{-t})/2` has `c(1) = 3/8`, `c(2) = 5/32 > c(1)^2`
theorem sep_semigroup_cm :
    let c1 : Q := mkQ 3 8
    let c2 : Q := mkQ 5 32
    isPSD4 (choiPauliMat c1 c1 1) ∧
    isPSD4 (choiPauliMat c2 c2 1) ∧
    c1 * c1 < c2 := by
  refine ⟨?_, ?_, mkQ_lt_of (by decide)⟩
  · apply pauli_choi_psd_of_eigs <;> apply mkQ_le_of <;> decide
  · apply pauli_choi_psd_of_eigs <;> apply mkQ_le_of <;> decide

-- 2. `CM ⊊ CP-Div`: rational witness `g(t) = (1 + t) / (1 + t + t^2)` is strictly decreasing
--    and positive for `0 ≤ s < t` (hence strictly CP-divisible!), yet violates midpoint convexity
--    (`g(0) + g(1) - 2 g(1/2) = -1/21 < 0`), hence cannot be completely monotonic.
def gRatCP (t : F) : F := (1 + t) / (1 + t + t * t)

theorem gRatCP_strictly_decreasing {F : Type} [OrderedField F] {s t : F}
    (hs : 0 ≤ s) (hst : s < t) :
    0 < gRatCP t ∧ gRatCP t < gRatCP s := by
  have ht : 0 < t := lt_of_le_of_lt hs hst
  have hds : 0 < 1 + s + s * s :=
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (zero_lt_one (F := F)) hs) (sq_nonneg s)
  have hdt : 0 < 1 + t + t * t :=
    add_pos_of_pos_of_nonneg (add_pos (zero_lt_one (F := F)) ht) (sq_nonneg t)
  have hnumt : 0 < 1 + t := add_pos (zero_lt_one (F := F)) ht
  refine ⟨div_pos hnumt hdt, ?_⟩
  have hts : 0 < t - s := sub_pos_of_lt hst
  have hsum : 0 < s + t + s * t :=
    add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hs ht)
      (OrderedField.mul_nonneg hs (le_of_lt ht))
  have hpos : 0 < (t - s) * (s + t + s * t) := OrderedField.mul_pos hts hsum
  have hdiff : (1 + s) * (1 + t + t * t) - (1 + t) * (1 + s + s * s) = (t - s) * (s + t + s * t) := by
    have hL : (1 + s) * (1 + t + t * t) = (1 + t + s + s * t) + (t * t + s * (t * t)) := by
      rw [right_distrib, CommField.one_mul, CommField.left_distrib, CommField.left_distrib, mul_one]
      calc (1 + t + t * t) + (s + s * t + s * (t * t))
          = ((1 + t) + t * t) + ((s + s * t) + s * (t * t)) := rfl
        _ = ((1 + t) + (s + s * t)) + (t * t + s * (t * t)) := add4_mid _ _ _ _
        _ = (1 + t + s + s * t) + (t * t + s * (t * t)) := by rw [← CommField.add_assoc (1 + t) s (s * t)]
    have hR : (1 + t) * (1 + s + s * s) = (1 + t + s + s * t) + (s * s + t * (s * s)) := by
      rw [right_distrib, CommField.one_mul, CommField.left_distrib, CommField.left_distrib, mul_one]
      have hst_eq : t * s = s * t := CommField.mul_comm t s
      have hst2 : (1 + s) + (t + t * s) = 1 + t + s + s * t := by
        rw [add4_mid, hst_eq, ← CommField.add_assoc]
      calc (1 + s + s * s) + (t + t * s + t * (s * s))
          = ((1 + s) + (t + t * s)) + (s * s + t * (s * s)) := add4_mid _ _ _ _
        _ = (1 + t + s + s * t) + (s * s + t * (s * s)) := by rw [hst2]
    have hsub1 : ((1 + t + s + s * t) + (t * t + s * (t * t))) - ((1 + t + s + s * t) + (s * s + t * (s * s)))
        = (t * t + s * (t * t)) - (s * s + t * (s * s)) := by
      rw [sub_def, neg_add, CommField.add_assoc,
          add_left_comm (t * t + s * (t * t)) (-(1 + t + s + s * t)),
          ← CommField.add_assoc (1 + t + s + s * t) (-(1 + t + s + s * t)),
          CommField.add_neg_cancel, CommField.zero_add, ← sub_def]
    have hsub2 : (t * t + s * (t * t)) - (s * s + t * (s * s)) = (t - s) * (s + t + s * t) := by
      have h1 : t * t - s * s = (t - s) * (t + s) := by
        rw [sub_mul, CommField.left_distrib, CommField.left_distrib, CommField.mul_comm s t,
            sub_def, sub_def, neg_add, CommField.add_assoc (t * t) (t * s),
            ← CommField.add_assoc (t * s) (-(t * s)), CommField.add_neg_cancel, CommField.zero_add]
      have h2 : s * (t * t) - t * (s * s) = (t - s) * (s * t) := by
        rw [sub_mul, mul_left_comm t s t, ← CommField.mul_assoc s s t, CommField.mul_comm (s * s) t]
      have h3 : (t * t + s * (t * t)) - (s * s + t * (s * s))
          = (t * t - s * s) + (s * (t * t) - t * (s * s)) := by
        rw [sub_def, sub_def, sub_def, neg_add, add4_mid]
      rw [h3, h1, h2, ← CommField.left_distrib, CommField.add_comm t s]
    rw [hL, hR, hsub1, hsub2]
  have hcross : (1 + t) * (1 + s + s * s) < (1 + s) * (1 + t + t * t) :=
    lt_of_sub_pos (by rwa [hdiff])
  unfold gRatCP
  rw [div_lt_iff_of_pos hdt]
  have hstep : (1 + t) * (1 + s + s * s) * FieldOps.inv (1 + s + s * s)
      < ((1 + s) * (1 + t + t * t)) * FieldOps.inv (1 + s + s * s) :=
    mul_lt_mul_of_pos_right hcross (inv_pos_of_pos hds)
  rw [CommField.mul_assoc (1 + t) (1 + s + s * s),
      CommField.mul_inv_cancel (1 + s + s * s) (ne_of_gt hds), mul_one,
      mul_right_comm (1 + s) (1 + t + t * t) (FieldOps.inv (1 + s + s * s))] at hstep
  exact hstep

private theorem gRatCP_0_eq : gRatCP (0 : Q) = 1 := by
  unfold gRatCP
  have h1 : (1 + (0 : Q) + 0 * 0) = mkQ 1 1 := by apply mkQ_eq_of; decide
  rw [h1]
  change (1 + (0 : Q)) * FieldOps.inv (mkQ 1 1) = 1
  rw [q_inv_mkQ_pos (n := 1) (d := 1) (by decide) (by decide)]
  apply mkQ_eq_of; decide

private theorem gRatCP_half_eq : gRatCP (mkQ 1 2) = mkQ 6 7 := by
  unfold gRatCP
  have h1 : (1 + mkQ 1 2 + mkQ 1 2 * mkQ 1 2) = mkQ 7 4 := by apply mkQ_eq_of; decide
  rw [h1]
  change (1 + mkQ 1 2) * FieldOps.inv (mkQ 7 4) = mkQ 6 7
  rw [q_inv_mkQ_pos (n := 7) (d := 4) (by decide) (by decide)]
  apply mkQ_eq_of; decide

private theorem gRatCP_1_eq : gRatCP (1 : Q) = mkQ 2 3 := by
  unfold gRatCP
  have h1 : (1 + (1 : Q) + 1 * 1) = mkQ 3 1 := by apply mkQ_eq_of; decide
  rw [h1]
  change (1 + (1 : Q)) * FieldOps.inv (mkQ 3 1) = mkQ 2 3
  rw [q_inv_mkQ_pos (n := 3) (d := 1) (by decide) (by decide)]
  apply mkQ_eq_of; decide

theorem sep_cm_cpdiv_midpoint_nonconvex :
    let g0 : Q := gRatCP (0 : Q)
    let gHalf : Q := gRatCP (mkQ 1 2)
    let g1 : Q := gRatCP (1 : Q)
    isPSD4 (choiPauliMat (gHalf / g0) (gHalf / g0) 1) ∧
    isPSD4 (choiPauliMat (g1 / gHalf) (g1 / gHalf) 1) ∧
    g0 + g1 < (1 + 1 : Q) * gHalf := by
  dsimp
  rw [gRatCP_0_eq, gRatCP_half_eq, gRatCP_1_eq]
  change isPSD4 (choiPauliMat (mkQ 6 7 * FieldOps.inv (mkQ 1 1)) (mkQ 6 7 * FieldOps.inv (mkQ 1 1)) 1) ∧
         isPSD4 (choiPauliMat (mkQ 2 3 * FieldOps.inv (mkQ 6 7)) (mkQ 2 3 * FieldOps.inv (mkQ 6 7)) 1) ∧
         (1 : Q) + mkQ 2 3 < (1 + 1 : Q) * mkQ 6 7
  rw [q_inv_mkQ_pos (n := 1) (d := 1) (by decide) (by decide),
      q_inv_mkQ_pos (n := 6) (d := 7) (by decide) (by decide)]
  refine ⟨?_, ?_, mkQ_lt_of (by decide)⟩
  · apply pauli_choi_psd_of_eigs <;> apply mkQ_le_of <;> decide
  · apply pauli_choi_psd_of_eigs <;> apply mkQ_le_of <;> decide

-- 3. `CP-Div ⊊ P-Div/BLP`: Eternal non-Markovian Pauli witness `r_x = r_y = 5/6, r_z = 1/2`
theorem sep_cpdiv_pdiv_eternal :
    let rx : Q := mkQ 5 6
    let ry : Q := mkQ 5 6
    let rz : Q := mkQ 1 2
    ((0 : Q) < rx ∧ rx < 1) ∧
    ((0 : Q) < ry ∧ ry < 1) ∧
    ((0 : Q) < rz ∧ rz < 1) ∧
    quadForm4 (choiPauliMat rx ry rz) ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩⟩ = mkQ (-1) 12 ∧
    quadForm4 (choiPauliMat rx ry rz) ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩⟩ < 0 := by
  refine ⟨⟨mkQ_lt_of (by decide), mkQ_lt_of (by decide)⟩,
          ⟨mkQ_lt_of (by decide), mkQ_lt_of (by decide)⟩,
          ⟨mkQ_lt_of (by decide), mkQ_lt_of (by decide)⟩, ?_, ?_⟩
  · rw [pauli_choi_witness_z]
    change (mkQ 1 1 - mkQ 5 6 - mkQ 5 6 + mkQ 1 2) * FieldOps.inv (mkQ 2 1) = mkQ (-1) 12
    rw [q_inv_mkQ_pos (n := 2) (d := 1) (by decide) (by decide)]; apply mkQ_eq_of; decide
  · rw [pauli_choi_witness_z]
    change (mkQ 1 1 - mkQ 5 6 - mkQ 5 6 + mkQ 1 2) * FieldOps.inv (mkQ 2 1) < 0
    rw [q_inv_mkQ_pos (n := 2) (d := 1) (by decide) (by decide)]; apply mkQ_lt_of; decide

private theorem q_div_four (a : Q) : a / ofNatF (F := Q) 4 = a * mkQ 1 4 := by
  change a * FieldOps.inv (ofNatF (F := Q) 4) = a * mkQ 1 4
  rw [q_ofNatF_4, q_inv_mkQ_pos (n := 4) (d := 1) (by decide) (by decide)]
  apply congrArg (a * ·)
  apply mkQ_eq_of
  decide

-- 4. `P-Div ⊊ Spohn-Monotone`: Non-unital qubit channel (`r_* = (0,0,4/5)`, `s = 1/20`, `K_xz = 9/5`)
--    Universal Gershgorin sum-of-rank-1 decomposition proving CPTP for ALL `t ≥ 1` simultaneously!

def gershgorinNonUnitalMat (d0 d1 d2 d3 p01 p03 n23 : F) : M4 F :=
  m4AddR (rank1Mat d0 ⟨1, 0, 0, 0⟩)
    (m4AddR (rank1Mat d1 ⟨0, 1, 0, 0⟩)
      (m4AddR (rank1Mat d2 ⟨0, 0, 1, 0⟩)
        (m4AddR (rank1Mat d3 ⟨0, 0, 0, 1⟩)
          (m4AddR (rank1Mat p01 ⟨1, 1, 0, 0⟩)
            (m4AddR (rank1Mat p03 ⟨1, 0, 0, 1⟩)
                    (rank1Mat n23 ⟨0, 0, 1, -1⟩))))))

theorem gershgorinNonUnital_isPSD {d0 d1 d2 d3 p01 p03 n23 : F}
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hp01 : 0 ≤ p01) (hp03 : 0 ≤ p03) (hn23 : 0 ≤ n23) :
    isPSD4 (ofRealM4 (gershgorinNonUnitalMat d0 d1 d2 d3 p01 p03 n23)) := by
  intro v
  rw [quadForm4_ofRealM4]
  have hreal : ∀ x : V4 F, 0 ≤ realQuad4 (gershgorinNonUnitalMat d0 d1 d2 d3 p01 p03 n23) x := by
    intro x
    unfold gershgorinNonUnitalMat
    rw [realQuad4_add, realQuad4_add, realQuad4_add, realQuad4_add, realQuad4_add, realQuad4_add,
        realQuad4_rank1, realQuad4_rank1, realQuad4_rank1, realQuad4_rank1,
        realQuad4_rank1, realQuad4_rank1, realQuad4_rank1]
    exact add_nonneg (OrderedField.mul_nonneg hd0 (sq_nonneg _))
      (add_nonneg (OrderedField.mul_nonneg hd1 (sq_nonneg _))
        (add_nonneg (OrderedField.mul_nonneg hd2 (sq_nonneg _))
          (add_nonneg (OrderedField.mul_nonneg hd3 (sq_nonneg _))
            (add_nonneg (OrderedField.mul_nonneg hp01 (sq_nonneg _))
              (add_nonneg (OrderedField.mul_nonneg hp03 (sq_nonneg _))
                (OrderedField.mul_nonneg hn23 (sq_nonneg _)))))))
  exact add_nonneg (hreal (v4Re v)) (hreal (v4Im v))

private theorem choiNonUnitalReal_eq_gershgorin (a b c mx mz : F) :
    let four := ofNatF (F := F) 4
    let s00 := (1 + mz + c) / four
    let s01 := (mx + b) / four
    let s03 := ((1 + 1 : F) * a) / four
    let s11 := (1 - mz - c) / four
    let s22 := (1 + mz - c) / four
    let s23 := (mx - b) / four
    let s33 := (1 - mz + c) / four
    choiNonUnitalReal a b c mx mz =
      gershgorinNonUnitalMat
        (s00 - s01 - s03) (s11 - s01) (s22 + s23) (s33 - s03 + s23)
        s01 s03 (-s23) := by
  intro four s00 s01 s03 s11 s22 s23 s33
  unfold choiNonUnitalReal gershgorinNonUnitalMat m4AddR rank1Mat
  dsimp only
  simp only [mul_zero, zero_mul, mul_one, CommField.one_mul, add_zero, CommField.zero_add,
             mul_neg, neg_mul, neg_mul_neg, neg_neg, neg_zero]
  have h00 : s00 = s00 - s01 - s03 + (s01 + s03) := by
    rw [CommField.add_comm s01 s03, ← CommField.add_assoc, sub_add_cancel, sub_add_cancel]
  have h11 : s11 = s11 - s01 + s01 := (sub_add_cancel s11 s01).symm
  have h22 : s22 = s22 + s23 + -s23 := by
    rw [CommField.add_assoc, CommField.add_neg_cancel, add_zero]
  have h33 : s33 = s33 - s03 + s23 + (s03 + -s23) := by
    rw [CommField.add_assoc (s33 - s03) s23 (s03 + -s23),
        CommField.add_comm s03 (-s23), ← CommField.add_assoc s23 (-s23) s03,
        CommField.add_neg_cancel, CommField.zero_add, sub_add_cancel]
  apply m4_ext <;> apply v4_ext <;> first | rfl | exact h00 | exact h11 | exact h22 | exact h33

/--
  Universal Gershgorin diagonal-dominance CPTP theorem for the 5-parameter non-unital
  qubit channel family over any `OrderedField F`.
-/
theorem choiNonUnital_isPSD_of_gershgorin {a b c mx mz : F}
    (h01 : 0 ≤ mx + b)
    (h03 : 0 ≤ a)
    (h23 : 0 ≤ b - mx)
    (hd0 : 0 ≤ (1 + mz + c) - (mx + b) - (1 + 1 : F) * a)
    (hd1 : 0 ≤ (1 - mz - c) - (mx + b))
    (hd2 : 0 ≤ (1 + mz - c) + (mx - b))
    (hd3 : 0 ≤ (1 - mz + c) - (1 + 1 : F) * a + (mx - b)) :
    isPSD4 (choiNonUnitalMat a b c mx mz) := by
  unfold choiNonUnitalMat
  rw [choiNonUnitalReal_eq_gershgorin]
  have h4pos : (0 : F) < ofNatF 4 := ofNatF_4_pos
  have hp01 : 0 ≤ (mx + b) / ofNatF 4 := div_nonneg h01 h4pos
  have hp03 : 0 ≤ ((1 + 1 : F) * a) / ofNatF 4 :=
    div_nonneg (OrderedField.mul_nonneg (le_of_lt (two_pos (F := F))) h03) h4pos
  have hn23 : 0 ≤ -((mx - b) / ofNatF 4) := by
    have hneg : -((mx - b) / ofNatF 4) = (b - mx) / ofNatF 4 := by
      change -((mx - b) * FieldOps.inv (ofNatF 4)) = (b - mx) * FieldOps.inv (ofNatF 4)
      rw [← neg_mul, sub_def, neg_add, neg_neg, CommField.add_comm, ← sub_def]
    rw [hneg]
    exact div_nonneg h23 h4pos
  have hgd0 : 0 ≤ (1 + mz + c) / ofNatF 4 - (mx + b) / ofNatF 4 - ((1 + 1 : F) * a) / ofNatF 4 := by
    rw [div_four_sub_div_four, div_four_sub_div_four]
    exact div_nonneg hd0 h4pos
  have hgd1 : 0 ≤ (1 - mz - c) / ofNatF 4 - (mx + b) / ofNatF 4 := by
    rw [div_four_sub_div_four]
    exact div_nonneg hd1 h4pos
  have hgd2 : 0 ≤ (1 + mz - c) / ofNatF 4 + (mx - b) / ofNatF 4 := by
    rw [div_four_add_div_four]
    exact div_nonneg hd2 h4pos
  have hgd3 : 0 ≤ (1 - mz + c) / ofNatF 4 - ((1 + 1 : F) * a) / ofNatF 4 + (mx - b) / ofNatF 4 := by
    rw [div_four_sub_div_four, div_four_add_div_four]
    exact div_nonneg hd3 h4pos
  exact gershgorinNonUnital_isPSD hgd0 hgd1 hgd2 hgd3 hp01 hp03 hn23

/--
  Exact fixed-point preservation for the Level 5 non-unital channel `Φ_t` with `r_* = (0, 0, 4/5)`:
  for every `(a, b, c)`, setting `m_x = -(4/5) b` and `m_z = (4/5)(1 - c)` guarantees
  `T r_* + m = r_*` identically.
-/
theorem sep_pdiv_spohn_fixed_point (a b c : Q) :
    let rstar_z : Q := mkQ 4 5
    let mx : Q := -(mkQ 4 5) * b
    let mz : Q := (mkQ 4 5) * (1 - c)
    a * 0 + b * rstar_z + mx = 0 ∧
    c * rstar_z + mz = rstar_z := by
  dsimp only
  constructor
  · rw [mul_zero, CommField.zero_add, neg_mul, CommField.mul_comm b (mkQ 4 5), CommField.add_neg_cancel]
  · rw [mul_sub, mul_one, CommField.mul_comm c (mkQ 4 5), sub_def,
        CommField.add_comm (mkQ 4 5) (-(mkQ 4 5 * c)), ← CommField.add_assoc,
        CommField.add_neg_cancel, CommField.zero_add]

/--
  **Uniform Global CPTP Certificate for Level 5 (`Φ_t` for ALL `t ≥ 1`)**:
  For EVERY triple `(a, b, c) ∈ [0, 1/20]^3` with exact fixed-point translation
  `m_x = -(4/5) b`, `m_z = (4/5)(1 - c)` preserving `r_* = (0, 0, 4/5)`, the Choi matrix
  `J(Φ_t)` is strictly diagonally dominant and hence positive semidefinite (`isPSD4`).
  Since for all `t ≥ 1` (`τ = t - 1 ≥ 0`), `a(τ) = (1/20) 2^{-τ} ∈ (0, 1/20]`,
  `c(τ) = (1/20) (5/2)^{-τ} ∈ (0, 1/20]`, and `0 ≤ b(τ) ≤ 0.04128 < 1/20`,
  this certifies global CPTP of the Level 5 witness for every `t ≥ 1` simultaneously.
-/
theorem sep_pdiv_spohn_uniform_cptp {a b c : Q}
    (ha0 : (0 : Q) ≤ a) (ha1 : a ≤ mkQ 1 20)
    (hb0 : (0 : Q) ≤ b) (hb1 : b ≤ mkQ 1 20)
    (hc0 : (0 : Q) ≤ c) (hc1 : c ≤ mkQ 1 20) :
    isPSD4 (choiNonUnitalMat a b c (-(mkQ 4 5) * b) ((mkQ 4 5) * (1 - c))) := by
  have q_neg_le : ∀ {u v : Q}, u ≤ v → -v ≤ -u := by
    intro u v huv
    have hp := sub_nonneg_of_le huv
    rw [sub_def] at hp
    exact le_of_sub_nonneg (by rwa [sub_def, neg_neg, CommField.add_comm])
  have h15 : (1 : Q) - mkQ 4 5 = mkQ 1 5 := by apply mkQ_eq_of; decide
  have h95 : (1 : Q) + mkQ 4 5 = mkQ 9 5 := by apply mkQ_eq_of; decide
  have h2a_le : (1 + 1 : Q) * a ≤ mkQ 1 10 := by
    have h := mul_le_mul_of_nonneg_left ha1 (le_of_lt (two_pos (F := Q)))
    have hval : (1 + 1 : Q) * mkQ 1 20 = mkQ 1 10 := by apply mkQ_eq_of; decide
    rwa [hval] at h
  have h_mx_add_b : -(mkQ 4 5) * b + b = mkQ 1 5 * b := by
    calc -(mkQ 4 5) * b + b = (1 + -(mkQ 4 5)) * b := by
          rw [right_distrib, CommField.one_mul, CommField.add_comm]
      _ = (1 - mkQ 4 5) * b := by rw [← sub_def]
      _ = mkQ 1 5 * b := by rw [h15]
  have h_b_sub_mx : b - -(mkQ 4 5) * b = mkQ 9 5 * b := by
    calc b - -(mkQ 4 5) * b = b + mkQ 4 5 * b := by rw [sub_def, neg_mul, neg_neg]
      _ = (1 + mkQ 4 5) * b := by rw [right_distrib, CommField.one_mul]
      _ = mkQ 9 5 * b := by rw [h95]
  have h_mx_sub_b : -(mkQ 4 5) * b - b = -(mkQ 9 5 * b) := by
    calc -(mkQ 4 5) * b - b = -(mkQ 4 5 * b) + -b := by rw [sub_def, neg_mul]
      _ = -(mkQ 4 5 * b + b) := (neg_add _ _).symm
      _ = -((mkQ 4 5 + 1) * b) := by rw [right_distrib, CommField.one_mul]
      _ = -(mkQ 9 5 * b) := by rw [CommField.add_comm (mkQ 4 5) 1, h95]
  have h_1pmz_pc : 1 + mkQ 4 5 * (1 - c) + c = mkQ 9 5 + mkQ 1 5 * c := by
    rw [mul_sub, mul_one, sub_def, ← CommField.add_assoc 1 (mkQ 4 5), h95,
        CommField.add_assoc (mkQ 9 5), CommField.add_comm (-(mkQ 4 5 * c)) c]
    congr 1
    calc c + -(mkQ 4 5 * c) = (1 - mkQ 4 5) * c := by
          rw [sub_mul, CommField.one_mul, sub_def]
      _ = mkQ 1 5 * c := by rw [h15]
  have h_1mmz_mc : 1 - mkQ 4 5 * (1 - c) - c = mkQ 1 5 - mkQ 1 5 * c := by
    rw [mul_sub, mul_one, sub_def, sub_def, sub_def, neg_add, neg_neg,
        ← CommField.add_assoc 1 (-(mkQ 4 5)), ← sub_def 1 (mkQ 4 5), h15,
        CommField.add_assoc (mkQ 1 5)]
    congr 1
    calc mkQ 4 5 * c + -c = -( (1 - mkQ 4 5) * c ) := by
          rw [sub_mul, CommField.one_mul, sub_def, neg_add, neg_neg, CommField.add_comm]
      _ = -(mkQ 1 5 * c) := by rw [h15]
  have h_1pmz_mc : 1 + mkQ 4 5 * (1 - c) - c = mkQ 9 5 - mkQ 9 5 * c := by
    rw [mul_sub, mul_one, sub_def, sub_def, sub_def,
        ← CommField.add_assoc 1 (mkQ 4 5), h95, CommField.add_assoc (mkQ 9 5)]
    congr 1
    calc -(mkQ 4 5 * c) + -c = -((1 + mkQ 4 5) * c) := by
          rw [right_distrib, CommField.one_mul, neg_add, CommField.add_comm]
      _ = -(mkQ 9 5 * c) := by rw [h95]
  have h_1mmz_pc : 1 - mkQ 4 5 * (1 - c) + c = mkQ 1 5 + mkQ 9 5 * c := by
    rw [mul_sub, mul_one, sub_def, sub_def, neg_add, neg_neg,
        ← CommField.add_assoc 1 (-(mkQ 4 5)), ← sub_def 1 (mkQ 4 5), h15,
        CommField.add_assoc (mkQ 1 5)]
    congr 1
    calc mkQ 4 5 * c + c = (1 + mkQ 4 5) * c := by
          rw [right_distrib, CommField.one_mul, CommField.add_comm]
      _ = mkQ 9 5 * c := by rw [h95]
  have h0_15 : (0 : Q) ≤ mkQ 1 5 := mkQ_le_of (by decide)
  have h0_95 : (0 : Q) ≤ mkQ 9 5 := mkQ_le_of (by decide)
  have h15b_le : mkQ 1 5 * b ≤ mkQ 1 100 := by
    have h := mul_le_mul_of_nonneg_left hb1 h0_15
    have hval : mkQ 1 5 * mkQ 1 20 = mkQ 1 100 := by apply mkQ_eq_of; decide
    rwa [hval] at h
  have h15c_le : mkQ 1 5 * c ≤ mkQ 1 100 := by
    have h := mul_le_mul_of_nonneg_left hc1 h0_15
    have hval : mkQ 1 5 * mkQ 1 20 = mkQ 1 100 := by apply mkQ_eq_of; decide
    rwa [hval] at h
  have h95b_le : mkQ 9 5 * b ≤ mkQ 9 100 := by
    have h := mul_le_mul_of_nonneg_left hb1 h0_95
    have hval : mkQ 9 5 * mkQ 1 20 = mkQ 9 100 := by apply mkQ_eq_of; decide
    rwa [hval] at h
  have h95c_le : mkQ 9 5 * c ≤ mkQ 9 100 := by
    have h := mul_le_mul_of_nonneg_left hc1 h0_95
    have hval : mkQ 9 5 * mkQ 1 20 = mkQ 9 100 := by apply mkQ_eq_of; decide
    rwa [hval] at h
  have h15c_nn : (0 : Q) ≤ mkQ 1 5 * c := OrderedField.mul_nonneg h0_15 hc0
  have h95c_nn : (0 : Q) ≤ mkQ 9 5 * c := OrderedField.mul_nonneg h0_95 hc0
  apply choiNonUnital_isPSD_of_gershgorin
  · rw [h_mx_add_b]; exact OrderedField.mul_nonneg h0_15 hb0
  · exact ha0
  · rw [h_b_sub_mx]; exact OrderedField.mul_nonneg h0_95 hb0
  · rw [h_1pmz_pc, h_mx_add_b, sub_def, sub_def]
    have hlo : (0 : Q) ≤ (mkQ 9 5 + 0) + -(mkQ 1 100) + -(mkQ 1 10) := mkQ_le_of (by decide)
    exact OrderedField.le_trans hlo
      (add_le_add (add_le_add (OrderedField.add_le_add_left _ h15c_nn) (q_neg_le h15b_le)) (q_neg_le h2a_le))
  · rw [h_1mmz_mc, h_mx_add_b, sub_def, sub_def]
    have hlo : (0 : Q) ≤ (mkQ 1 5 + -(mkQ 1 100)) + -(mkQ 1 100) := mkQ_le_of (by decide)
    exact OrderedField.le_trans hlo
      (add_le_add (OrderedField.add_le_add_left _ (q_neg_le h15c_le)) (q_neg_le h15b_le))
  · rw [h_1pmz_mc, h_mx_sub_b, sub_def]
    have hlo : (0 : Q) ≤ (mkQ 9 5 + -(mkQ 9 100)) + -(mkQ 9 100) := mkQ_le_of (by decide)
    exact OrderedField.le_trans hlo
      (add_le_add (OrderedField.add_le_add_left _ (q_neg_le h95c_le)) (q_neg_le h95b_le))
  · rw [h_1mmz_pc, h_mx_sub_b, sub_def]
    have hlo : (0 : Q) ≤ ((mkQ 1 5 + 0) + -(mkQ 1 10)) + -(mkQ 9 100) := mkQ_le_of (by decide)
    exact OrderedField.le_trans hlo
      (add_le_add (add_le_add (OrderedField.add_le_add_left _ h95c_nn) (q_neg_le h2a_le)) (q_neg_le h95b_le))

theorem sep_pdiv_spohn_phi1_cptp :
    isPSD4 (choiNonUnitalMat (mkQ 1 20) 0 (mkQ 1 20) 0 (mkQ 19 25)) := by
  have h := sep_pdiv_spohn_uniform_cptp (a := mkQ 1 20) (b := 0) (c := mkQ 1 20)
    (mkQ_le_of (by decide)) (mkQ_le_of (by decide))
    (OrderedField.le_refl 0) (mkQ_le_of (by decide))
    (mkQ_le_of (by decide)) (mkQ_le_of (by decide))
  have hmx : -(mkQ 4 5) * (0 : Q) = 0 := mul_zero _
  have hmz : (mkQ 4 5) * (1 - mkQ 1 20) = mkQ 19 25 := by apply mkQ_eq_of; decide
  rwa [hmx, hmz] at h

theorem sep_pdiv_spohn_phi2_cptp :
    isPSD4 (choiNonUnitalMat (mkQ 11 250) (mkQ 3 200) (mkQ 21 500) (mkQ (-3) 250) (mkQ 479 625)) := by
  have h := sep_pdiv_spohn_uniform_cptp (a := mkQ 11 250) (b := mkQ 3 200) (c := mkQ 21 500)
    (mkQ_le_of (by decide)) (mkQ_le_of (by decide))
    (mkQ_le_of (by decide)) (mkQ_le_of (by decide))
    (mkQ_le_of (by decide)) (mkQ_le_of (by decide))
  have hmx : -(mkQ 4 5) * mkQ 3 200 = mkQ (-3) 250 := by apply mkQ_eq_of; decide
  have h1c : (1 : Q) - mkQ 21 500 = mkQ 479 500 := by apply mkQ_eq_of; decide
  have hmz : (mkQ 4 5) * (1 - mkQ 21 500) = mkQ 479 625 := by rw [h1c]; apply mkQ_eq_of; decide
  rwa [hmx, hmz] at h

/--
  Interval-certified local BKM vs. Euclidean BLP separation for `K = diag(-ln 2, -ln 2, -ln(5/2)) + (9/5) E_{xz}`
  around `r_* = (0, 0, 4/5)` where `g_zz = 25/9` and `g_xx = (5/4) ln 3 ∈ [137/100, 138/100]`:
  Euclidean norm expands along `(1, 0, 1)` (`euclidShearForm > 0`), while the linearized BKM Fisher
  contractivity quadratic form (`bkmShearDecayForm`) at `r_*` is strictly positive definite for all `v ≠ 0`
  (global nonlinear Spohn monotonicity over the pre-contracted reachable ball `‖r - r_*‖ ≤ 0.095`,
  containing the true reachable radius `0.090000 < 0.093479 < 0.095`, is verified numerically).
-/
theorem sep_pdiv_spohn_bkm_vs_blp
    {kxx kzz gxx : Q}
    (hkxx_lo : mkQ (-70) 100 ≤ kxx) (hkxx_hi : kxx ≤ mkQ (-69) 100)
    (hkzz_lo : mkQ (-92) 100 ≤ kzz) (hkzz_hi : kzz ≤ mkQ (-91) 100)
    (hgxx_lo : mkQ 137 100 ≤ gxx) (hgxx_hi : gxx ≤ mkQ 138 100)
    (vx vy vz : Q) (hnz : vx ≠ 0 ∨ vy ≠ 0 ∨ vz ≠ 0) :
    (0 : Q) < euclidShearForm kxx (mkQ 9 5) kzz 1 0 1 ∧
    (0 : Q) < bkmShearDecayForm kxx (mkQ 9 5) kzz gxx (mkQ 25 9) vx vy vz := by
  have heuc_simp : ∀ u v : Q, euclidShearForm u (mkQ 9 5) v 1 0 1 = (1 + 1 : Q) * (u + v + mkQ 9 5) := by
    intro u v
    unfold euclidShearForm
    rw [mul_one, mul_zero, mul_zero, add_zero, mul_one, mul_one, mul_one]
  have heuc_bnd : (0 : Q) < (1 + 1 : Q) * (mkQ (-70) 100 + mkQ (-92) 100 + mkQ 9 5) := by
    apply mkQ_lt_of; decide
  have heuc_mono : (1 + 1 : Q) * (mkQ (-70) 100 + mkQ (-92) 100 + mkQ 9 5)
      ≤ euclidShearForm kxx (mkQ 9 5) kzz 1 0 1 := by
    rw [heuc_simp]
    exact mul_le_mul_of_nonneg_left
      (add_le_add_right (mkQ 9 5) (add_le_add hkxx_lo hkzz_lo)) (le_of_lt (two_pos (F := Q)))
  refine ⟨lt_of_lt_of_le heuc_bnd heuc_mono, ?_⟩
  unfold bkmShearDecayForm
  have le_neg_of_le : ∀ u v : Q, u ≤ v → -v ≤ -u := by
    intro u v huv
    have hp := sub_nonneg_of_le huv
    rw [sub_def] at hp
    exact le_of_sub_nonneg (by rwa [sub_def, neg_neg, CommField.add_comm])
  have hnkxx : mkQ 69 100 ≤ -kxx := by
    have h := le_neg_of_le kxx (mkQ (-69) 100) hkxx_hi
    have heq : -(mkQ (-69) 100) = mkQ 69 100 := by apply mkQ_eq_of; decide
    rwa [heq] at h
  have hnkzz : mkQ 91 100 ≤ -kzz := by
    have h := le_neg_of_le kzz (mkQ (-91) 100) hkzz_hi
    have heq : -(mkQ (-91) 100) = mkQ 91 100 := by apply mkQ_eq_of; decide
    rwa [heq] at h
  have htwo_pos : (0 : Q) < 1 + 1 := two_pos (F := Q)
  have hkxx_pos : (0 : Q) < -kxx := lt_of_lt_of_le (mkQ_lt_of (by decide)) hnkxx
  have hgxx_pos : (0 : Q) < gxx := lt_of_lt_of_le (mkQ_lt_of (by decide)) hgxx_lo
  have hmul_mono : ∀ {a₁ a₂ b₁ b₂ : Q}, 0 ≤ a₁ → 0 ≤ b₁ → a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ * b₁ ≤ a₂ * b₂ :=
    fun ha₁ hb₁ ha hb =>
      OrderedField.le_trans
        (mul_le_mul_of_nonneg_right ha hb₁)
        (mul_le_mul_of_nonneg_left hb (OrderedField.le_trans ha₁ ha))
  have ha_lo : (1 + 1 : Q) * mkQ 69 100 * mkQ 137 100 ≤ (1 + 1 : Q) * (-kxx) * gxx :=
    hmul_mono
      (OrderedField.mul_nonneg (le_of_lt htwo_pos) (mkQ_le_of (by decide)))
      (mkQ_le_of (by decide))
      (mul_le_mul_of_nonneg_left hnkxx (le_of_lt htwo_pos))
      hgxx_lo
  have hc_lo : (1 + 1 : Q) * mkQ 91 100 * mkQ 25 9 ≤ (1 + 1 : Q) * (-kzz) * mkQ 25 9 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnkzz (le_of_lt htwo_pos))
      (mkQ_le_of (by decide))
  have ha_pos : (0 : Q) < (1 + 1 : Q) * (-kxx) * gxx :=
    OrderedField.mul_pos (OrderedField.mul_pos htwo_pos hkxx_pos) hgxx_pos
  have hb_eq : (-gxx * mkQ 9 5) * (-gxx * mkQ 9 5) = (gxx * mkQ 9 5) * (gxx * mkQ 9 5) := by
    rw [neg_mul, neg_mul_neg]
  have hb_hi : (-gxx * mkQ 9 5) * (-gxx * mkQ 9 5)
      ≤ (mkQ 138 100 * mkQ 9 5) * (mkQ 138 100 * mkQ 9 5) := by
    rw [hb_eq]
    have hm : gxx * mkQ 9 5 ≤ mkQ 138 100 * mkQ 9 5 :=
      mul_le_mul_of_nonneg_right hgxx_hi (mkQ_le_of (by decide))
    have hnn : 0 ≤ gxx * mkQ 9 5 := OrderedField.mul_nonneg (le_of_lt hgxx_pos) (mkQ_le_of (by decide))
    exact hmul_mono hnn hnn hm hm
  have hac_lo : ((1 + 1 : Q) * mkQ 69 100 * mkQ 137 100) * ((1 + 1 : Q) * mkQ 91 100 * mkQ 25 9)
      ≤ ((1 + 1 : Q) * (-kxx) * gxx) * ((1 + 1 : Q) * (-kzz) * mkQ 25 9) :=
    hmul_mono
      (OrderedField.mul_nonneg (OrderedField.mul_nonneg (le_of_lt htwo_pos) (mkQ_le_of (by decide))) (mkQ_le_of (by decide)))
      (OrderedField.mul_nonneg (OrderedField.mul_nonneg (le_of_lt htwo_pos) (mkQ_le_of (by decide))) (mkQ_le_of (by decide)))
      ha_lo hc_lo
  have hdet_bnd :
      ((1 + 1 : Q) * mkQ 69 100 * mkQ 137 100) * ((1 + 1 : Q) * mkQ 91 100 * mkQ 25 9)
      - (mkQ 138 100 * mkQ 9 5) * (mkQ 138 100 * mkQ 9 5)
      ≤ ((1 + 1 : Q) * (-kxx) * gxx) * ((1 + 1 : Q) * (-kzz) * mkQ 25 9)
        - (-gxx * mkQ 9 5) * (-gxx * mkQ 9 5) := by
    rw [sub_def, sub_def]
    exact add_le_add hac_lo (le_neg_of_le _ _ hb_hi)
  have hdet_pos_bnd :
      (0 : Q) < ((1 + 1 : Q) * mkQ 69 100 * mkQ 137 100) * ((1 + 1 : Q) * mkQ 91 100 * mkQ 25 9)
        - (mkQ 138 100 * mkQ 9 5) * (mkQ 138 100 * mkQ 9 5) := by
    apply mkQ_lt_of; decide
  exact sylvester_quad3_pos ha_pos (lt_of_lt_of_le hdet_pos_bnd hdet_bnd) ha_pos hnz

-- 5. `Spohn-Monotone ⊊ CPTP`: Coherence revival witness `c_1 = 1/2 < c_2 = 3/4`
theorem sep_spohn_cptp :
    let c1 : Q := mkQ 1 2
    let c2 : Q := mkQ 3 4
    isPSD4 (choiPauliMat c1 c1 1) ∧
    isPSD4 (choiPauliMat c2 c2 1) ∧
    c1 * c1 < c2 * c2 := by
  refine ⟨?_, ?_, mkQ_lt_of (by decide)⟩
  · apply pauli_choi_psd_of_eigs <;> apply mkQ_le_of <;> decide
  · apply pauli_choi_psd_of_eigs <;> apply mkQ_le_of <;> decide

end Ordered4x4

end ChoiAndHierarchy

/-! ## Axiom Verification Checks (Must show only standard Lean axioms or none) -/

#print axioms hankel_propagator_numerator_im
#print axioms hankel_derivative_numerator_im
#print axioms cm_spectral_numerator_pos
#print axioms single_sign_change_below
#print axioms single_sign_change_above
#print axioms overdamped_no_nonneg_real_root
#print axioms real_root_strictly_neg
#print axioms underdamped_no_real_roots
#print axioms underdamped_complex_root_char
#print axioms pole_wedge_boundary_iff
#print axioms subdiffusive_always_pole_free
#print axioms single_sign_change_integral_pos
#print axioms geom_partial_sum_identity
#print axioms geom_tail_archimedean_bound
#print axioms pauli_choi_fujiwara_algoet
#print axioms pauli_subordination_cp_sufficient
#print axioms pauli_subord_mu095_counterexample
#print axioms sep_semigroup_cm
#print axioms gRatCP_strictly_decreasing
#print axioms sep_cm_cpdiv_midpoint_nonconvex
#print axioms sep_cpdiv_pdiv_eternal
#print axioms choiNonUnital_isPSD_of_gershgorin
#print axioms sep_pdiv_spohn_fixed_point
#print axioms sep_pdiv_spohn_uniform_cptp
#print axioms sep_pdiv_spohn_phi1_cptp
#print axioms sep_pdiv_spohn_phi2_cptp
#print axioms sep_pdiv_spohn_bkm_vs_blp
#print axioms sep_spohn_cptp

end DiamondProofs.Paper2




