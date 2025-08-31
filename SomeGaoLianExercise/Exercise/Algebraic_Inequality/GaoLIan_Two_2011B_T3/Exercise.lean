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


theorem GL2011BT3 {a b c : ℝ} (h : a * b * c + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + c * a - c * b - 4 * a + 4 * b - c = 28)
            (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
            a + b + c ≤ 6 ∧ ∃ a₀ b₀ c₀ : ℝ, a₀ * b₀ * c₀ + 2 * a₀ ^ 2 + 2 * b₀ ^ 2 + 2 * c₀ ^ 2 + c₀ * a₀ - c₀ * b₀ - 4 * a₀ + 4 * b₀ - c₀ = 28 := by
  sorry







end section
