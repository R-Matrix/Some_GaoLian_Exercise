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
  have : n - 1 + 1 = n := by omega
  have ez_eq1 : ∑ k ∈ Finset.range n, a k = (n : ℝ) * A (n - 1) := by
    unfold A; field_simp; rw[this]
  have ez_eq2 : (n : ℝ) * A (n - 1) - ∑ k ∈ Finset.range n, A k = ∑ k ∈ Finset.range (n-1), (A (n - 1) - A k) := by
    nth_rw 1 [←Finset.card_range n, ←nsmul_eq_mul, ←Finset.sum_const (A (n - 1)), ←Finset.sum_sub_distrib, ←this]
    rw[Finset.sum_range_succ]; simp
  rw[ez_eq1, ez_eq2]
  apply Finset.abs_sum_le_sum_abs

lemma e1 {n k : ℕ} (hn : 3 ≤ n) (hk : k < n - 1) : A (n - 1) - A k
        = (1 / n : ℝ) * (∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i)) - (1 / (k + 1) - 1 / n: ℝ) * (∑ i ∈ Finset.range (k + 1), a i)
          := by
  unfold A; simp only; norm_cast
  have this1 : n - 1 + 1 = n := by omega
  have this2 : n - (k + 1) + (k + 1) = n := by omega
  rw[this1]; nth_rw 1 [←this2, add_comm, Finset.sum_range_add]
  rw[add_comm, add_div, ←add_sub]; congr
  · rw[one_div_mul_eq_div]
  · rw[sub_mul, one_div_mul_eq_div, one_div_mul_eq_div]; simp

lemma le1 (k : ℕ) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
      0 < ∑ i ∈ Finset.range (k + 1), a i∧ ∑ i ∈ Finset.range (k + 1), a i ≤ (k + 1) := by
  constructor
  · rw[←Finset.sum_const_zero]; apply Finset.sum_lt_sum; simp; intro i _; linarith[hai0 i]; use 0; simp; apply hai0
  · norm_cast;
    have : ∀ i ∈ Finset.range (k + 1), a i ≤ 1 := fun i _ ↦ hai1 i
    apply le_trans (Finset.sum_le_sum this); simp

lemma le2 {n k : ℕ} (hn : 3 ≤ n) (hk : k < n - 1) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
      0 < ∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i)
        ∧ ∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i) ≤ n - (k + 1) := by
  constructor
  · rw[←Finset.sum_const_zero]; apply Finset.sum_lt_sum; simp; intro i _; linarith[hai0 (k + 1 + i)];
    use 0; simp; exact ⟨by omega, hai0 _⟩
  · have : ∀ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i) ≤ 1 := fun i _ ↦ hai1 (k + 1 + i)
    apply le_trans (Finset.sum_le_sum this); simp
    have : k + 1 ≤ n := by omega
    norm_cast

lemma step2 {n k : ℕ} (hn : 3 ≤ n) (hk : k < n - 1) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
      |A (n - 1) - A k| < 1 - ((k + 1) / n : ℝ) := by
  apply abs_lt.mpr; rw[e1 hn hk]; constructor
  · have h1 : (1 / (k + 1) - 1 / n) * ∑ i ∈ Finset.range (k + 1), a i ≤ 1 - ((k + 1) / n : ℝ) := by
      have this1 : 0 < (1 / (k + 1) - 1 / n : ℝ) := by field_simp; norm_cast; omega
      have this2 : 1 - ((k + 1) / n : ℝ) = (1 / (k + 1) - 1 / n : ℝ) * ((k : ℝ) + 1) := by field_simp; ring
      have := (mul_le_mul_iff_of_pos_left this1).mpr (le1 k hai0 hai1).2
      rwa[←this2] at this
    have h2 : (1 / n : ℝ) * ∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i) > 0 := by
      have this1 : 1 / (n : ℝ) > 0 := by field_simp; linarith
      have this2 : ∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i) > 0 := (le2 hn hk hai0 hai1).1
      nlinarith
    linarith
  · have h1 : 1 / (n : ℝ) * ∑ i ∈ Finset.range (n - (k + 1)), a (k + 1 + i) ≤ 1 - ((k + 1) / n : ℝ) := by
      field_simp;
      have this1 :=(le2 hn hk hai0 hai1).2
      have this2 : (n : ℝ) > 0 := by simp; linarith
      apply (div_le_div_iff_of_pos_right this2).mpr this1
    have h2 : (1 / (k + 1) - 1 / n : ℝ) * ∑ i ∈ Finset.range (k + 1), a i > 0 := by
      have this1 : 0 < (1 / (k + 1) - 1 / n : ℝ) := by field_simp; norm_cast; omega
      have this2 := (le1 k hai0 hai1).1
      nlinarith
    linarith

lemma step3 {n : ℕ} (hn : 3 ≤ n) :
        ∑ k ∈ Finset.range (n - 1), (1 - ((k + 1) / n : ℝ)) = (n - 1) / (2 : ℝ) := by
  simp; field_simp;
  rw[sub_mul];
  have : (∑ x ∈ Finset.range (n - 1), (x + 1) / n : ℝ) * 2 = n - 1 := by
    rw[←Finset.sum_div, Finset.sum_add_distrib]; simp; field_simp; rw[add_mul];
    rw[←Nat.cast_sum , ←Nat.cast_two ,←Nat.cast_mul,Finset.sum_range_id_mul_two (n - 1)]
    have hn1 : (n - 1 : ℝ) = (n - 1 : ℕ) := by rw[Nat.cast_sub]; simp; omega
    have hn2 : (n - 2 : ℝ) = (n - 1 - 1 : ℕ) := by rw[Nat.cast_sub, Nat.cast_sub]; norm_num; linarith; omega; omega
    rw[Nat.cast_mul, ←hn1, ←hn2]; ring
  rw[this]; ring


theorem GL2010T3 {n : ℕ} (hn : 3 ≤ n) (hai0 : ∀ i : ℕ, 0 < a i) (hai1 : ∀ i : ℕ, a i ≤ 1) :
        |((∑ k ∈ Finset.range n, a k) - (∑ k ∈ Finset.range n, A k))| < (n - 1) / (2 : ℝ) :=
   lt_of_le_of_lt (step1 hn) (lt_of_lt_of_eq (Finset.sum_lt_sum (fun _ hi ↦ le_of_lt (step2 hn (Finset.mem_range.mp hi) hai0 hai1)) ⟨0, ⟨by simp; omega, step2 hn (by omega) hai0 hai1⟩⟩) (step3 hn))




--  by
--     apply lt_of_le_of_lt
--     apply step1 hn
--     apply lt_of_lt_of_eq
--     apply Finset.sum_lt_sum
--     · intro i hi
--       apply le_of_lt (step2 hn (Finset.mem_range.mp hi) hai0 hai1)
--     · use 0; constructor; simp; omega; apply step2 hn (by omega) hai0 hai1
--     apply step3 hn



end section
