import Mathlib.Data.Real.Basic

import SomeGaoLianExercise


/-
# 2005 年高中联赛 二试

## 第二题

设正数 $a, b, c, x, y, z$ 满足 $cy + bz = a$, $az + cx = b$, $bx + ay = c$, 求函数
$$ f(x, y, z) = \frac{x ^ 2}{1 + x} + \frac{y ^ 2}{1 + y} + \frac{z ^ 2}{1 + z} $$
的最小值.

---

## 答案

$$\frac 12$$
-/

section

#check Finset.sum_mul_sq_le_sq_mul_sq    --求和形式的 Cauchy-Schwarz Inequality
#check Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
#check important_Inequality

noncomputable def f := fun (x y z : ℝ) ↦ (x ^ 2) / (1 + x) + (y ^ 2) / (1 + y) + (z ^ 2) / (1 + z)

variable {a b c x y z : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
         (hx : x > 0) (hy : y > 0) (hz : z > 0)
         (e1 : a = c * y + b * z) (e2 : b = a * z + c * x) (e3 : c = b * x + a * y)

example : f x y z ≥ 1 / 2 :=
  sorry

lemma xyze (ha : a > 0) (hb : b > 0) (hc : c > 0)
         (hx : x > 0) (hy : y > 0) (hz : z > 0)
         (e1 : a = c * y + b * z) (e2 : b = a * z + c * x) (e3 : c = b * x + a * y) :
         x = (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) ∧ y = (c ^ 2 + a ^ 2 - b ^ 2) / (2 * c * a) ∧ z = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) :=
  sorry

lemma Radon's_inequality {a b c x y z : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
         (hx : x > 0) (hy : y > 0) (hz : z > 0) :
          a ^ 2 / x + b ^ 2 / y + c ^ 2 / z ≥ (a + b + c) ^ 2 / (x + y + z) := by
      sorry

lemma Shur's_inequality {a b c : ℝ} : 0 ≤ a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - c) * (b - a) + c ^ 2 * (c - a) * (c - b) := by
  sorry

theorem GL2005T2 : (x ^ 2) / (1 + x) + (y ^ 2) / (1 + y) + (z ^ 2) / (1 + z) ≥ 1 / 2 ∧
      ∃ x₀ y₀ z₀ : ℝ, f x₀ y₀ z₀ = 1 / 2:= by
  sorry

end section
