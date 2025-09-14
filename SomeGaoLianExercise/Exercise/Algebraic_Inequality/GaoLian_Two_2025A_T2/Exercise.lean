import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Basic

import SomeGaoLianExercise

/-!
# 2025 年高中联赛 $\cdot$ 二试(A卷)

## 第二题

设 $m, n, k$ 都是正整数, $m \ge 2$, 且 $n \ge k \ge 2$.

实数 $x_1 \ge x_2 \ge \cdots \ge x_n \ge 0$, 满足以下两个条件:

1. $x_1 ^ m + x_2 ^ m + \cdots + x _ n ^ m \ge 1$.

2. $x_1 + x_2 + \cdots + x_n \le k$.

证明 : $x_1 + x_2 + \cdots + x_k \ge 1$

---

## 答案

**反证法**. 假设 $x_1 + x_2 + \cdots + x_k < 1$, 我们有

$$1 > x_1 \ge x_2 \ge \cdots \ge x_k \ge 0.$$

设 $x_k = u$, 则 $u \le \dfrac{x_1 + x_2 + \cdots + x_k}{k} < \dfrac 1k$, 又 $m \ge 2$, 故

$$\sum _{i = k+1} ^ n x_i ^m \le \sum _{i = k+1} ^ n x_i ^ 2 \le \sum _{i = k+1} ^ n x_k x_i= u \sum_{i = k+1}^n x_i ,$$

结合两个条件知

$$
\sum _{i = 1}^k x_i ^ m \ge 1 - \sum _{i= k+1}^n x_i^m \ge 1 - u \sum _{i= k+1} ^ n x_i \ge 1 - u \left(k - \sum_{i = 1} ^ k x_i \right)
$$

利用 $x_i ^ m \le x_i ^ 2$ 及 $x_i - u \ge 0 (1 \le i \le k)$, 得

$$
\begin{align*}
    1 - uk &\le \sum_{i = 1}^k x_i ^m - u\sum _{i = 1}^k x_i \le \sum_{i = 1}^k x_i ^2 - u\sum _{i = 1}^k x_i = \sum _{i = 1} ^ k x_i (x_i - u)\\ &\le \sum _{i = 1} ^k (x_i - u) = \sum _{i =1}^k x_i -uk
\end{align*}
$$

这与假设 $x_1 + x_2 + \cdots + x_k < 1$ 矛盾!

因此原命题成立. $\square$

-/

section

def x_ : ℕ → ℝ := sorry

variable (n k m : ℕ) (u : ℝ)
variable (hn : 2 ≤ n)
variable (hm : 2 ≤ m)
variable (hk : 2 ≤ k)
variable (hkn : k ≤ n)
variable (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i)
variable (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i)
variable (hx1 : 1 ≤ ∑ i ∈ Finset.range n, (x_ i) ^ m)
variable (hx2 : ∑ i ∈ Finset.range n, x_ i ≤ k)
variable (xku : x_ (k - 1) = u)

example : 1 ≤ ∑ i ∈ Finset.range k , x_ i :=
  sorry


#check Finset.sum_insert
#check Finset.sum_erase_add
#check Finset.sum_range_add
#check Finset.smul_sum


lemma xk_isMin : ∀ i : ℕ, 0 ≤ i ∧ i ≤ k - 1 → 0 ≤ x_ i - u := sorry

lemma xk_isMax : ∀ i : ℕ, k ≤ i ∧ i ≤ n - 1 → x_ i ≤ u := sorry

lemma hx_le_one (hx0 : ∑ i ∈ Finset.range k, x_ i < 1) : ∀ i, i ∈ Finset.range n → x_ i < 1 := by
  sorry

lemma ineq_0 : ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ m ≤ ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ 2 := by
  sorry

lemma ineq_0' (hx_le_one : ∀ i, i ∈ Finset.range k → x_ i < 1) :  ∑ i ∈ Finset.range k, (x_ i) ^ m ≤ ∑ i ∈ Finset.range k, (x_ i) ^ 2 := by
  sorry

lemma ineq_1 (hx_le_one : ∀ i, i ∈ Finset.range k → x_ i < 1) : ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ m ≤ u * ∑ i ∈ Finset.range (n - k), x_ (i + k) := by
  sorry

lemma ineq2 (ineq1 : ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ m ≤ u * ∑ i ∈ Finset.range (n - k), x_ (i + k)):
        1 - u * (k - ∑ i ∈ Finset.range k, x_ i) ≤ ∑ i ∈ Finset.range k, (x_ i) ^ m := by
  sorry

lemma ineq3 (hx0 : ∑ i ∈ Finset.range k, x_ i < 1)
            (ineq0' : ∑ i ∈ Finset.range k, (x_ i) ^ m ≤ ∑ i ∈ Finset.range k, (x_ i) ^ 2)
            (ineq2 : 1 - u * (k - ∑ i ∈ Finset.range k, x_ i) ≤ ∑ i ∈ Finset.range k, (x_ i) ^ m) :
        1 - u * k ≤ (∑ i ∈ Finset.range k, x_ i) - u * k := by
  sorry

theorem GL2025AT2 (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k) (hkn : k ≤ n) (xku : x_ (k - 1) = u)
          (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i) (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i)
          (hx1 : 1 ≤ ∑ i ∈ Finset.range n, (x_ i) ^ m ) (hx2 : ∑ i ∈ Finset.range n, x_ i ≤ k) :
      1 ≤ ∑ i ∈ Finset.range k , x_ i := by
  sorry


end section
