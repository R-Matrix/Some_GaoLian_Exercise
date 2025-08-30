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

lemma pow_two_phi : (√5 + 1) / 2 + 1 = ((√5 + 1) / 2) ^ 2 := by
  ring_nf; norm_num; linarith

lemma x0ephi {n : ℕ} (hx0e : x_ 0 = (√ 5 + 1) / 2) : x_ n = (√ 5 + 1) / 2 := by
  induction' n with n h
  · trivial
  · unfold x_
    rw [h, Real.sqrt_eq_iff_eq_sq, pow_two_phi];
    linarith[Real.sqrt_nonneg 5]; linarith[Real.sqrt_nonneg 5]

lemma x0nephi (n : ℕ) (posx_ : ∀ n : ℕ, 0 < x_ n) (hx0ne : x_ 0 ≠ (√ 5 + 1) / 2) : x_ n ≠ (√ 5 + 1) / 2 := by
  induction' n with n h
  · trivial
  · intro h₀; apply h
    rw[x_ , Real.sqrt_eq_iff_eq_sq, ←pow_two_phi] at h₀; linarith
    linarith[posx_ n]; linarith[Real.sqrt_nonneg 5]

lemma x_keyeq {n : ℕ} (posx_ : ∀ n : ℕ, 0 < x_ n) : x_ (n + 1) - ((√5 + 1) / 2) = (x_ n - (√5 + 1) / 2) / (x_ (n + 1) + ((√5 + 1) / 2)) := by
  apply eq_div_of_mul_eq
  apply ne_of_gt (add_pos (posx_ (n+1)) (by linarith[Real.sqrt_nonneg 5]))
  rw[x_]
  ring_nf; rw[add_comm 1 ,Real.sq_sqrt (le_of_lt (add_pos (posx_ n) one_pos))]; norm_num; ring_nf;

lemma compe_ine (n : ℕ) (posx_ : ∀ n : ℕ, 0 < x_ n) (hx0ne : x_ 0 ≠ (√ 5 + 1) / 2) : |x_ (n + 1) - ((√5 + 1) / 2)| < |(x_ n - (√5 + 1) / 2)| / ((√5 + 1) / 2) := by
  have this1 : ((√5 + 1) / 2) > 0 := by linarith[Real.sqrt_nonneg 5]
  rw[x_keyeq posx_, abs_div]
  apply div_lt_div₀'
  · linarith
  · apply lt_abs.mpr; left; linarith[posx_ (n + 1)]
  · have := x0nephi n posx_ hx0ne
    apply abs_pos.mpr; intro h; apply this; linarith
  · linarith

lemma final_ineq {n : ℕ} (hn : 1 ≤ n) (posx_ : ∀ n : ℕ, 0 < x_ n) (hx0ne : x_ 0 ≠ (√ 5 + 1) / 2) : |x_ n - ((√5 + 1) / 2)| < |x₀ - ((√5 + 1) / 2)| / ((√5 + 1) / 2) ^ n := by
  induction' n with n h
  · linarith
  · apply lt_of_lt_of_le (compe_ine n posx_ hx0ne)
    by_cases hn' : n = 0
    · rw[hn', x_]; norm_num
    · push_neg at hn'; rw[←Nat.one_le_iff_ne_zero] at hn'
      apply le_of_lt
      apply (div_lt_iff₀ (by linarith[Real.sqrt_nonneg 5])).mpr
      apply lt_of_lt_of_eq (h hn')
      field_simp; ring

theorem GL2012BT3 (posx_ : ∀ n : ℕ, 0 < x_ n) : ∃ A C : ℝ , 1 < A ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |x_ n - A| < C / A ^ n := by
  use (√ 5 + 1) / 2
  by_cases x0e : x₀ = (√ 5 + 1) / 2
  · use 1
    constructor
    · have : 1 < √ 5 := by apply (Real.lt_sqrt (by norm_num)).mpr; norm_num
      linarith
    constructor
    · linarith
    · intro n
      rw[x0ephi x0e]; simp
      intro hn
      apply pow_pos; linarith[Real.sqrt_nonneg 5]
  · push_neg at x0e
    use |x₀ - (√ 5 + 1) / 2|
    constructor
    · have : 1 < √ 5 := by apply (Real.lt_sqrt (by norm_num)).mpr; norm_num
      linarith
    constructor
    · apply abs_pos.mpr; intro h; apply x0e; linarith
    · intro n hn
      apply final_ineq hn posx_ x0e














end section
