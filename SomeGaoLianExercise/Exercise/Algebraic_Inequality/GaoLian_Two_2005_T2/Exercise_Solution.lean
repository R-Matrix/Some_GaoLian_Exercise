import Mathlib.Data.Real.Basic

import SomeGaoLianExercise

set_option maxHeartbeats 400000

----------------------------------------------------------------------------------------------------------------
    /-
    # 2005 年高中联赛 · 二试

    ## 第二题

    设正数 $a, b, c, x, y, z$ 满足 $cy + bz = a$, $az + cx = b$, $bx + ay = c$, 求函数
    $$ f(x, y, z) = \frac{x ^ 2}{1 + x} + \frac{y ^ 2}{1 + y} + \frac{z ^ 2}{1 + z} $$
    的最小值.

    ---

    ## 答案

    $$\frac 12$$
    -/

---------------------------------------------------------------------------------------------------------------

section

noncomputable def f := fun (x y z : ℝ) ↦ (x ^ 2) / (1 + x) + (y ^ 2) / (1 + y) + (z ^ 2) / (1 + z)

variable {a b c x y z : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
         (hx : x > 0) (hy : y > 0) (hz : z > 0)
         (e1 : a = c * y + b * z) (e2 : b = a * z + c * x) (e3 : c = b * x + a * y)

example : f x y z ≥ 1 / 2 :=
  sorry

lemma xyze (ha : a > 0) (hb : b > 0) (hc : c > 0)
         (e1 : a = c * y + b * z) (e2 : b = a * z + c * x) (e3 : c = b * x + a * y) :
         x = (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) ∧ y = (c ^ 2 + a ^ 2 - b ^ 2) / (2 * c * a) ∧ z = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) := by
  have t1 : a ^ 2 = a * c * y + a * b * z := by rw[pow_two]; nth_rw 2 [e1]; linarith
  have t2 : b ^ 2 = b * a * z + b * c * x := by rw[pow_two]; nth_rw 2 [e2]; linarith
  have t3 : c ^ 2 = c * b * x + c * a * y := by rw[pow_two]; nth_rw 2 [e3]; linarith
  constructor
  · apply eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hb)) (ne_of_gt hc))
    linarith
  · constructor
    · apply eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hc)) (ne_of_gt ha))
      linarith
    · apply eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt ha)) (ne_of_gt hb))
      linarith

#check Finset.sum_mul_sq_le_sq_mul_sq    --求和形式的 Cauchy-Schwarz Inequality
#check Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
#check important_Inequality

lemma Radon's_inequality {a b c x y z : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
         (hx : x > 0) (hy : y > 0) (hz : z > 0) :
          a ^ 2 / x + b ^ 2 / y + c ^ 2 / z ≥ (a + b + c) ^ 2 / (x + y + z) := by
  apply div_le_of_le_mul₀ (le_of_lt (add_pos (add_pos hx hy) hz))
  apply add_nonneg (add_nonneg (div_nonneg (sq_nonneg a) (le_of_lt hx)) (div_nonneg (sq_nonneg b) (le_of_lt hy))) (div_nonneg (sq_nonneg c) (le_of_lt hz))
  have h1 : 2 * a * c ≤ a ^ 2 * z / x + c ^ 2 * x / z := by
    apply le_trans _ (important_Inequality (div_nonneg (mul_nonneg (sq_nonneg a) (le_of_lt hz)) (le_of_lt hx)) (div_nonneg (mul_nonneg (sq_nonneg c) (le_of_lt hx)) (le_of_lt hz)))
    ring_nf; field_simp
  have h2 : 2 * a * b ≤ a ^ 2 * y / x + b ^ 2 * x / y := by
    apply le_trans _ (important_Inequality (div_nonneg (mul_nonneg (sq_nonneg a) (le_of_lt hy)) (le_of_lt hx)) (div_nonneg (mul_nonneg (sq_nonneg b) (le_of_lt hx)) (le_of_lt hy)))
    ring_nf; field_simp
  have h3 : 2 * b * c ≤ b ^ 2 * z / y + c ^ 2 * y / z := by
    apply le_trans _ (important_Inequality (div_nonneg (mul_nonneg (sq_nonneg b) (le_of_lt hz)) (le_of_lt hy)) (div_nonneg (mul_nonneg (sq_nonneg c) (le_of_lt hy)) (le_of_lt hz)))
    ring_nf; field_simp
  calc
    (a ^ 2 / x + b ^ 2 / y + c ^ 2 / z) * (x + y + z)
    _= (a ^ 2 + b ^ 2 + c ^ 2) + (a ^ 2 * y / x + b ^ 2 * x / y) + (a ^ 2 * z / x + c ^ 2 * x / z) + (b ^ 2 * z / y  + c ^ 2 * y / z) := by field_simp; ring
    _≥ (a ^ 2 + b ^ 2 + c ^ 2) + 2 * a * b + 2 * a * c + 2 * b * c := by gcongr
    _= (a + b + c) ^ 2 := by ring

lemma Schur's_inequality {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c): 0 ≤ a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - c) * (b - a) + c ^ 2 * (c - a) * (c - b) := by
  wlog h : c ≤ b ∧ b ≤ a with hnt
  · push_neg at h
    by_cases h1 : c ≤ b
    · have h2 := h h1
      by_cases h3 : c ≤ a
      · have := hnt hb ha hc ⟨h3, le_of_lt h2⟩
        linarith
      · push_neg at h3
        have := hnt hb hc ha ⟨le_of_lt h3, h1⟩
        linarith
    · push_neg at h1
      by_cases h2 : a ≤ b
      · have := hnt hc hb ha ⟨h2, le_of_lt h1⟩
        linarith
      · push_neg at h2
        by_cases h3 : c ≤ a
        · have := hnt ha hc hb ⟨le_of_lt h1, h3⟩
          linarith
        · push_neg at h3
          have := hnt hc ha hb ⟨le_of_lt h2, le_of_lt h3⟩
          linarith
  have :  a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - c) * (b - a) + c ^ 2 * (c - a) * (c - b) = a ^ 2 * (a - b) ^ 2 + (a - b) * (b - c) * (a ^ 2 - b ^ 2 + c ^ 2) + c ^ 2 * (b - c) ^ 2 := by
    ring
  rw[this]
  have : 0 ≤ a ^ 2 - b ^ 2 + c ^ 2 := by nlinarith
  apply add_nonneg; apply add_nonneg
  · nlinarith
  · apply mul_nonneg (by nlinarith) this
  · nlinarith

lemma aux (ha : a > 0) (hb : b > 0) (hc : c > 0)
         (hx : x > 0) (hy : y > 0) (hz : z > 0)
         (e1 : a = c * y + b * z) (e2 : b = a * z + c * x) (e3 : c = b * x + a * y) :
         (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 * (2 * b * c) / ((2 * b * c) ^ 2 * (2 * b * c + (b ^ 2 + c ^ 2 - a ^ 2))) + (c ^ 2 + a ^ 2 - b ^ 2) ^ 2 * (2 * c * a) / ((2 * c * a) ^ 2 * (2 * c * a + (c ^ 2 + a ^ 2 - b ^ 2))) + (a ^ 2 + b ^ 2 - c ^ 2) ^ 2 * (2 * a * b) / ((2 * a * b) ^ 2 * (2 * a * b + (a ^ 2 + b ^ 2 - c ^ 2))) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / (2 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + a * b ^ 3 + b * c ^ 3 + c * a ^ 3) - a * b * c * (a + b + c))) := by
    have hab : 2 * a * b ≠ 0 := by nlinarith
    have hbc : 2 * b * c ≠ 0 := by nlinarith
    have hca : 2 * c * a ≠ 0 := by nlinarith
    field_simp
    have de1 : (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 * (2 * b * c) / ((2 * b * c) ^ 2 * (2 * b * c + (b ^ 2 + c ^ 2 - a ^ 2))) = (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 / (2 * b * c * (b ^ 2 + c ^ 2 + 2 * b * c - a ^ 2)) := by
      rw[mul_comm, pow_two (2 * b * c), mul_assoc (2 * b * c), mul_div_mul_left _ _ hbc]; ring
    have de2 : (c ^ 2 + a ^ 2 - b ^ 2) ^ 2 * (2 * c * a) / ((2 * c * a) ^ 2 * (2 * c * a + (c ^ 2 + a ^ 2 - b ^ 2))) = (c ^ 2 + a ^ 2 - b ^ 2) ^ 2 / (2 * c * a * (c ^ 2 + a ^ 2 + 2 * c * a - b ^ 2)) := by
      rw[mul_comm, pow_two (2 * c * a), mul_assoc (2 * c * a), mul_div_mul_left _ _ hca]; ring
    have de3 : (a ^ 2 + b ^ 2 - c ^ 2) ^ 2 * (2 * a * b) / ((2 * a * b) ^ 2 * (2 * a * b + (a ^ 2 + b ^ 2 - c ^ 2))) = (a ^ 2 + b ^ 2 - c ^ 2) ^ 2 / (2 * a * b * (a ^ 2 + b ^ 2 + 2 * a * b - c ^ 2)) := by
      rw[mul_comm, pow_two (2 * a * b), mul_assoc (2 * a * b), mul_div_mul_left _ _ hab]; ring
    have ie1 : 0 < a ^ 2 + b ^ 2 - c ^ 2 := by rw[(xyze ha hb hc e1 e2 e3).2.2] at hz; apply pos_of_mul_pos_left _ (le_of_lt (inv_pos.mpr (mul_pos (mul_pos (two_pos) (ha)) hb))); rwa[←div_eq_mul_inv];
    have ie2 : 0 < b ^ 2 + c ^ 2 - a ^ 2 := by rw[(xyze ha hb hc e1 e2 e3).1] at hx; apply pos_of_mul_pos_left _ (le_of_lt (inv_pos.mpr (mul_pos (mul_pos (two_pos) (hb)) hc))); rwa[←div_eq_mul_inv];
    have ie3 : 0 < c ^ 2 + a ^ 2 - b ^ 2 := by rw[(xyze ha hb hc e1 e2 e3).2.1] at hy; apply pos_of_mul_pos_left _ (le_of_lt (inv_pos.mpr (mul_pos (mul_pos (two_pos) (hc)) ha))); rwa[←div_eq_mul_inv];
    have ie4 : 0 < 2 * b * c * (b ^ 2 + c ^ 2 + 2 * b * c - a ^ 2) := by apply mul_pos (by nlinarith); rw[add_comm]; nlinarith
    have ie5 : 0 < 2 * c * a * (c ^ 2 + a ^ 2 + 2 * c * a - b ^ 2) := by apply mul_pos (by nlinarith); rw[add_comm]; nlinarith
    have ie6 : 0 < 2 * a * b * (a ^ 2 + b ^ 2 + 2 * a * b - c ^ 2) := by rw[add_comm]; apply mul_pos; nlinarith; nlinarith
    have ez1 : (b ^ 2 + c ^ 2 - a ^ 2 + (c ^ 2 + a ^ 2 - b ^ 2) + (a ^ 2 + b ^ 2 - c ^ 2)) = (a ^ 2 + b ^ 2 + c ^ 2) := by linarith
    have ez2 : (2 * b * c * (b ^ 2 + c ^ 2 + 2 * b * c - a ^ 2) + 2 * c * a * (c ^ 2 + a ^ 2 + 2 * c * a - b ^ 2) + 2 * a * b * (a ^ 2 + b ^ 2 + 2 * a * b - c ^ 2)) = 2 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + a * b ^ 3 + b * c ^ 3 + c * a ^ 3) - a * b * c * (a + b + c)) := by ring
    calc
      _= (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 / (2 * b * c * (b ^ 2 + c ^ 2 + 2 * b * c - a ^ 2)) + (c ^ 2 + a ^ 2 - b ^ 2) ^ 2 / (2 * c * a * (c ^ 2 + a ^ 2 + 2 * c * a - b ^ 2)) + (a ^ 2 + b ^ 2 - c ^ 2) ^ 2 / (2 * a * b * (a ^ 2 + b ^ 2 + 2 * a * b - c ^ 2)) := by rw[de1, de2, de3]
      _≥ ((b ^ 2 + c ^ 2 - a ^ 2) + (c ^ 2 + a ^ 2 - b ^ 2) + (a ^ 2 + b ^ 2 - c ^ 2)) ^ 2 / ((2 * b * c * (b ^ 2 + c ^ 2 + 2 * b * c - a ^ 2)) + (2 * c * a * (c ^ 2 + a ^ 2 + 2 * c * a - b ^ 2)) + (2 * a * b * (a ^ 2 + b ^ 2 + 2 * a * b - c ^ 2))) := by apply Radon's_inequality (le_of_lt ie2) (le_of_lt ie3) (le_of_lt ie1) ie4 ie5 ie6
      _= (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / (2 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  + (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + a * b ^ 3 + b * c ^ 3 + c * a ^ 3) - a * b * c * (a + b + c))) := by rw[ez1, ez2]


theorem GL2005T2 (ha : a > 0) (hb : b > 0) (hc : c > 0)
         (hx : x > 0) (hy : y > 0) (hz : z > 0)
         (e1 : a = c * y + b * z) (e2 : b = a * z + c * x) (e3 : c = b * x + a * y): 1 / 2 ≤ f x y z  ∧
      ∃ x₀ y₀ z₀ : ℝ, f x₀ y₀ z₀ = 1 / 2:= by
  constructor
  · unfold f
    rw[(xyze ha hb hc e1 e2 e3).1, (xyze ha hb hc e1 e2 e3).2.1, (xyze ha hb hc e1 e2 e3).2.2]
    field_simp
    apply le_trans _ (aux ha hb hc hx hy hz e1 e2 e3)
    rw[le_div_iff₀]
    have := Schur's_inequality (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
    apply le_of_sub_nonneg
    have h1 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 1 / 2 * (2 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + a * b ^ 3 + b * c ^ 3 + c * a ^ 3) - a * b * c * (a + b + c))) = a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - c) * (b - a) + c ^ 2 * (c - a) * (c - b) := by
      ring
    rwa[h1]
    have ez2 : (2 * b * c * (b ^ 2 + c ^ 2 + 2 * b * c - a ^ 2) + 2 * c * a * (c ^ 2 + a ^ 2 + 2 * c * a - b ^ 2) + 2 * a * b * (a ^ 2 + b ^ 2 + 2 * a * b - c ^ 2)) = 2 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + a * b ^ 3 + b * c ^ 3 + c * a ^ 3) - a * b * c * (a + b + c)) := by ring
    rw[←ez2]
    have ie1 : 0 < a ^ 2 + b ^ 2 - c ^ 2 := by rw[(xyze ha hb hc e1 e2 e3).2.2] at hz; apply pos_of_mul_pos_left _ (le_of_lt (inv_pos.mpr (mul_pos (mul_pos (two_pos) (ha)) hb))); rwa[←div_eq_mul_inv];
    have ie2 : 0 < b ^ 2 + c ^ 2 - a ^ 2 := by rw[(xyze ha hb hc e1 e2 e3).1] at hx; apply pos_of_mul_pos_left _ (le_of_lt (inv_pos.mpr (mul_pos (mul_pos (two_pos) (hb)) hc))); rwa[←div_eq_mul_inv];
    have ie3 : 0 < c ^ 2 + a ^ 2 - b ^ 2 := by rw[(xyze ha hb hc e1 e2 e3).2.1] at hy; apply pos_of_mul_pos_left _ (le_of_lt (inv_pos.mpr (mul_pos (mul_pos (two_pos) (hc)) ha))); rwa[←div_eq_mul_inv];
    have ie4 : 0 < 2 * b * c * (b ^ 2 + c ^ 2 + 2 * b * c - a ^ 2) := by apply mul_pos (by nlinarith); rw[add_comm]; nlinarith
    have ie5 : 0 < 2 * c * a * (c ^ 2 + a ^ 2 + 2 * c * a - b ^ 2) := by apply mul_pos (by nlinarith); rw[add_comm]; nlinarith
    have ie6 : 0 < 2 * a * b * (a ^ 2 + b ^ 2 + 2 * a * b - c ^ 2) := by rw[add_comm]; apply mul_pos; nlinarith; nlinarith
    linarith
  · use 1 / 2, 1 / 2, 1 / 2
    unfold f
    norm_num





end section
