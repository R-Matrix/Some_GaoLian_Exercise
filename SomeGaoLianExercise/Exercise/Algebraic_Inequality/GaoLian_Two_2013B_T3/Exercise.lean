import Mathlib.Data.Real.Basic

import SomeGaoLianExercise

/-
# 2012 年高中联赛 $\cdot$ 二试(B卷)

## 第三题

设非负实数 $x, y, z$ 满足 $x ^ 2 + y ^ 2 + z ^ 2 = 10$. 求

$$ u = \sqrt {6-x ^ 2} + \sqrt{6- y ^ 2 } + \sqrt {6 - z ^ 2} $$

的最大值和最小值.

---

## 答案

最大值为 $2\sqrt 6$, 最小值为 $\sqrt 6 + \sqrt 2$.
-/


section

variable (x y z : ℝ) (hx : 0 ≤ x ∧ x ^ 2 ≤ 6) (hy : 0 ≤ y ∧ y ^ 2 ≤ 6) (hz : 0 ≤ z ∧ z ^ 2 ≤ 6) (h : x ^ 2 + y ^ 2 + z ^ 2 = 10)

noncomputable def u : ℝ :=
  √ (6 - x ^ 2) + √ (6 - y ^ 2) + √ (6 - z ^ 2)

example : √ 6 + √ 2 ≤ u x y z ∧ ∃ x₀ y₀ z₀ : ℝ, u x₀ y₀ z₀ = √ 6 + √ 2 :=
  sorry

example : u x y z ≤ 2*  √ 6 ∧ ∃ x₀ y₀ z₀ : ℝ, u x₀ y₀ z₀ = 2 * √ 6 :=
  sorry



theorem GL2013BT3 (hx : 0 ≤ x ∧ x ^ 2 ≤ 6) (hy : 0 ≤ y ∧ y ^ 2 ≤ 6) (hz : 0 ≤ z ∧ z ^ 2 ≤ 6)
                  (h : x ^ 2 + y ^ 2 + z ^ 2 = 10) :
          √ 6 + √ 2 ≤ u x y z ∧ (∃ x₀ y₀ z₀ : ℝ, u x₀ y₀ z₀ = √ 6 + √ 2) ∧
          u x y z ≤ 2 * √ 6 ∧ ∃ x₀ y₀ z₀ : ℝ, u x₀ y₀ z₀ = 2 * √ 6 := by
  sorry


end section
