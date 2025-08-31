import Mathlib.Data.Real.Basic

import SomeGaoLianExercise



/-
-- # 2011 年高中联赛 $\cdot$ 二试 (B卷)

-- ## 第三题

-- 设实数 $a, b, c \ge 1$ , 且满足

-- $$abc + 2a^2 + 2b^2 + 2c^2 + ca - cb - 4a + 4b - c = 28.$$

-- 求 $a + b + c$ 的最大值

-- ---

-- ## 答案

-- $6$
-/

section

variable (a b c : ℝ) (h : a * b * c + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + c * a - c * b - 4 * a + 4 * b - c = 28)
        (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
example : a + b + c ≤ 6 ∧ ∃ a₀ b₀ c₀ : ℝ, a₀ * b₀ * c₀ + 2 * a₀ ^ 2 + 2 * b₀ ^ 2 + 2 * c₀ ^ 2 + c₀ * a₀ - c₀ * b₀ - 4 * a₀ + 4 * b₀ - c₀ = 28 :=
  sorry


lemma exists_mul_nonneg (a b c : ℝ) : (a * b) ≥ 0 ∨ (b * c) ≥ 0 ∨ (c * a) ≥ 0 := by
  rcases lt_or_ge a 0 with ha | ha
  · rcases lt_or_ge b 0 with hb | hb
    · left; nlinarith
    · rcases lt_or_ge c 0 with hc | hc
      · right; right; nlinarith
      · right; left; nlinarith
  · rcases lt_or_ge b 0 with hb | hb
    · rcases lt_or_ge c 0 with hc | hc
      · right; left; nlinarith
      · right; right; nlinarith
    · left; nlinarith

lemma ineq1 {x y : ℝ} (h : (2 - x) * (2 - y) ≥ 0) : x + y ≤ 1 / 2 * x * y + 2 := by
  nlinarith

lemma ineq2 (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 + 1 / 2 * x * y * z = 16) (hz : z ≥ 0) :
          1 / 2 * x * y ≤ 4 - z := by
  have : (4 - z) * (4 + z) = (x - y) ^ 2 + 1 / 2 * (z + 4) * x * y := by
    ring_nf; rw[←h]; ring
  nlinarith

lemma key_change {a b c : ℝ} (h : a * b * c + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + c * a - c * b - 4 * a + 4 * b - c = 28) :
          (a - 1) ^ 2 + (b + 1) ^ 2 + c ^ 2 + 1 / 2 * (a - 1) * (b + 1) * c = 16 := by
  nlinarith


theorem GL2011BT3 {a b c : ℝ} (h : a * b * c + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + c * a - c * b - 4 * a + 4 * b - c = 28)
            (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c):
            a + b + c ≤ 6 ∧ ∃ a₀ b₀ c₀ : ℝ, a₀ * b₀ * c₀ + 2 * a₀ ^ 2 + 2 * b₀ ^ 2 + 2 * c₀ ^ 2 + c₀ * a₀ - c₀ * b₀ - 4 * a₀ + 4 * b₀ - c₀ = 28 := by
  constructor
  · have := key_change h
    set x := a - 1 with x_def
    set y := b + 1 with y_def
    set z := c with z_def
    have hx : a = x + 1 := by linarith
    have hy : b = y - 1 := by linarith
    rw[hx, hy]; simp
    rcases exists_mul_nonneg (2 - x) (2 - y) (2 - z) with i1 | i1 | i1
    apply ineq1 at i1; have := ineq2 x y z (by linarith) (by linarith); nlinarith
    apply ineq1 at i1; have := ineq2 y z x (by linarith) (by linarith); nlinarith
    apply ineq1 at i1; have := ineq2 z x y (by linarith) (by linarith); nlinarith
  · use 3, 1, 2
    norm_num














end section
