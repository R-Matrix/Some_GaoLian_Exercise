import Mathlib.Data.Real.Basic

import SomeGaoLianExercise

/-
-----------------------------------------------------------------------------
    # 2012 年高中联赛 $\cdot$ 二试(B卷)

    ## 第三题

    设数列 $\{x _ n\}$ 满足 $x_0 > 0,  x_n = \sqrt{x _{n-1}  + 1}, n \ge 1$.
    求证 : 存在常数 $A$ 和 $C$ $(A > 1, C > 0)$ , 使得 $|x _ n - A|
    <  \dfrac{C}{A^n}$对任意正整数 $n$ 成立.

    ---

    ## 答案

    取 $A = \dfrac {1 + \sqrt 5}{2}$.

    当 $x _ 0 = A$ 时, $x _ n $ 恒等于 $A$, 此时取 $C$ 为任意正实数均可.

    当 $x_0  \ne A$ 时, 易知对任意正整数 $n$ , $x_n \ne A$.

    由 $x_n = \sqrt {x _ {n-1} + 1}$ 知, $x_n^2 - A^2 = x_{n-1} - A$, 所以

    $$|x_n - A| = \frac{|x_{n-1}-A|}{|x_n + A|} < \frac{|x_{n-1}- A|}{A}.$$

    累乘, 得

    $$|x_n - A| < \frac{|x_0 - A|}{A^n}$$

    所以取 $C = |x_0 - A|$ 即可.

    S综上, 命题得证. $\square$
-------------------------------------------------------------------------------
-/


section

def x₀ : ℝ := sorry

noncomputable def x_ : ℕ → ℝ
  | 0 => x₀
  | n + 1 => Real.sqrt (x_ n + 1)

variable (posx_ : ∀ n : ℕ, 0 < x_ n)

example : ∃ A C : ℝ , 1 < A ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |x_ n - A| < C / A ^ n :=
  sorry

theorem GL2012BT3 (posx_ : ∀ n : ℕ, 0 < x_ n) : ∃ A C : ℝ , 1 < A ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |x_ n - A| < C / A ^ n := by
  sorry


end section
