import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.MeanInequalities

section Cauchy's_Inequality

theorem pow_two_fun_nonneg_iff (a b c : ℝ) (ha : a > 0) : (∀ x : ℝ, 0 ≤ a * x ^ 2 + b * x + c) ↔ b ^ 2 - 4 * a * c ≤ 0 := by
  constructor
  · intro h
    by_contra! hn
    have h1 := h (- b / (2 * a))
    have h2 : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = c - b^2 / (4 * a) := by field_simp; ring
    rw[h2] at h1
    have : b ^ 2 - 4 * a * c ≤ 0 := by
      apply le_of_mul_le_mul_left _ (inv_pos.mpr (mul_pos four_pos ha))
      rw[mul_zero, mul_sub, ←mul_assoc, inv_mul_cancel₀ (mul_ne_zero four_ne_zero (ne_of_gt ha)), one_mul, inv_mul_eq_div, ←neg_zero]
      apply le_neg.mpr; rwa[neg_sub]
    linarith
  · intro h x
    calc
    a * x ^ 2 + b * x + c
    _= a * (x + b / (2 * a)) ^ 2 + (c - b ^ 2 / (4 * a)) := by field_simp; ring
    _≥ 0 + (c - b ^ 2 / (4 * a)) := by apply add_le_add_right; apply mul_nonneg (le_of_lt ha) (pow_two_nonneg (x + b / (2 * a)))
    _= (c - b ^ 2 / (4 * a)) := zero_add (c - b ^ 2 / (4 * a))
    _≥ 0 := by apply (mul_le_mul_right (mul_pos four_pos ha)).mp; rw[zero_mul, sub_mul, div_mul_cancel₀ (b ^ 2) (mul_ne_zero four_ne_zero (ne_of_gt ha)), mul_comm, ←neg_zero]; apply neg_le.mp; rwa[neg_sub]

theorem important_Inequality {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 2 * √ (a * b) ≤ a + b := by
  have := sq_nonneg (√ a - √ b)
  ring_nf at this
  rw[Real.sqrt_mul ha]; simp[ha, hb] at this
  linarith[this]
