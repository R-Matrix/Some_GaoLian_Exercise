import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Basic

import SomeGaoLianExercise

/-
##################################################################

# 2005 年高中联赛 $\cdot$ 二试

## 第三题

设整数 $n \ge 3$ , 正实数 $\alpha_1, \alpha_2, \cdots , \alpha_n$
满足 $a_k \le 1, k = 1, 2, \cdots n$. 对 $1 \le k \le n$,
记$A_k = \dfrac{a_1 + a_2 + \cdots + a_n}{k} $.

求证 :
$$\left|\sum_{k=1}^n a_k-\sum _{k = 1} ^ n A_k\right| < \frac {n-1} 2.$$

---

## 答案

由三角不等式,
$$\left| \sum_{k=1}^n a_k - \sum_{k=1}^n A_k \right|
= \left| nA_n - \sum _{k = 1} ^ n A_k  \right|
= \left|\sum _{k=1}^{n-1}(A_n - A_k) \right|
\le \sum_{k=1}^{n-1} \left|A_n - A_k \right|.$$

对 $1 \le k \le n-1 $,
$$A_n - A_k = \frac 1n \sum_{i=1}^n a_i -\frac 1k \sum_{i =1}^n a_i
= \frac 1n\sum _{i=k + 1}^n a_i -
\left(\frac 1k-\frac 1n\right)\sum_{i=1}^k a_i
$$

由 $0 < a_i \le 1$ 知,

$$0 < \sum_{i = 1}^k a_i \le k,
\qquad 0 < \sum_{i=k+1}^n a_i \le n - k$$

所以
$$\frac 1n\sum_{i=k+1}^n a_i-\left(\frac 1k-\frac 1n\right)\sum_{i=1}^ka_i
< \frac 1n (n-k) = 1-\frac kn $$

$$\frac 1n\sum_{i=k+1}^n a_i-\left(\frac 1k-\frac 1n\right)\sum_{i=1}^ka_i
> - \left(\frac 1k - \frac 1n\right) k = - \left(1- \frac kn\right) $$

从而 $|A_n - A_k | < 1 - \dfrac kn .$

这样,

$$\left| \sum_{k=1}^n a_k - \sum_{k=1}^n A_k \right|
\le \sum_{k=1}^{n-1} \left|A_n - A_k \right|
< \sum_{k = 1}^{n-1} \left(1 - \dfrac kn \right)
= \frac {n-1}{2}.\quad \square$$

##################################################################
-/

section

def a : ℕ → ℝ := sorry

noncomputable def A : ℕ → ℝ :=
  fun n => match n with
  | n => (∑ i ∈ Finset.range (n + 1), a i) / (n + 1)

--    请注意 :  ∑ i ∈ Finset.range n, a i = `a 0 + a 1 + ... + a (n - 1)`
--    这里规定 A 0 = a 0


variable (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1)


example {n : ℕ} (hn : 3 ≤ n) : |((∑ k ∈ Finset.range n, a k) - (∑ k ∈ Finset.range n, A k))| < (n - 1) / (2 : ℝ) := by
  sorry

#check Finset.abs_sum_le_sum_abs
#check Finset.sum_sub_distrib
#check Finset.mul_sum
#check Finset.sum_const
#check Finset.card_range
#check Finset.sum_lt_sum
#check Finset.sum_range_add
#check Finset.sum_range_succ
#check Finset.sum_range_id_mul_two


lemma step1 {n : ℕ} (hn : 3 ≤ n) :
  |((∑ k ∈ Finset.range n, a k) - (∑ k ∈ Finset.range n, A k))|
      ≤ ∑ k ∈ Finset.range (n - 1), |A (n - 1) - A k| := by
  sorry

lemma e1 {n k : ℕ} (hn : 3 ≤ n) (hk : k < n - 1) : A (n - 1) - A k
        = (1 / n : ℝ) * (∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i)) - (1 / (k + 1) - 1 / n: ℝ) * (∑ i ∈ Finset.range (k + 1), a i)
          := by
  sorry

lemma le1 (k : ℕ) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
      0 < ∑ i ∈ Finset.range (k + 1), a i ∧ ∑ i ∈ Finset.range (k + 1), a i ≤ (k + 1) := by
  sorry

lemma le2 {n k : ℕ} (hn : 3 ≤ n) (hk : k < n - 1) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
      0 < ∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i)
        ∧ ∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i) ≤ n - (k + 1) := by
  sorry

lemma step2 {n k : ℕ} (hn : 3 ≤ n) (hk : k < n - 1) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
      |A (n - 1) - A k| < 1 - ((k + 1) / n : ℝ) := by
  sorry

lemma step3 {n : ℕ} (hn : 3 ≤ n) :
        ∑ k ∈ Finset.range (n - 1), (1 - ((k + 1) / n : ℝ)) = (n - 1) / (2 : ℝ) := by
  sorry


theorem GL2010T3 {n : ℕ} (hn : 3 ≤ n) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
        |((∑ k ∈ Finset.range n, a k) - (∑ k ∈ Finset.range n, A k))| < (n - 1) / (2 : ℝ) :=
  sorry













end section
