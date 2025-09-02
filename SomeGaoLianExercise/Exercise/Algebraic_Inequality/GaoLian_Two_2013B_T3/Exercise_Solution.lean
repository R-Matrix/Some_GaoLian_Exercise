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

#check Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul

lemma CS_ineq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc :  0 ≤ c) :
          √ a + √ b + √ c ≤ √ (3 * (a + b + c)) := by
  let s : Finset ℕ := Finset.range 3
  let f : ℕ → ℝ := fun _ ↦ (1 : ℝ)
  let g : ℕ → ℝ
        | 0 => a
        | 1 => b
        | 2 => c
        | _ => 0
  let r : ℕ → ℝ
        | 0 => √ a
        | 1 => √ b
        | 2 => √ c
        | _ => 0
  have hf : ∀ i ∈ s, 0 ≤ f i := by
    intro i hi
    unfold f; norm_num
  have hg : ∀ i ∈ s, 0 ≤ g i := by
    intro i hi
    unfold g
    match i with
    | 0 => simp[ha]
    | 1 => simp[hb]
    | 2 => simp[hc]
  have ht : ∀ i ∈ s, r i ^ 2 = f i * g i := by
    intro i hi
    unfold f g r
    match i with
    | 0 => simp[Real.sq_sqrt ha]
    | 1 => simp[Real.sq_sqrt hb]
    | 2 => simp[Real.sq_sqrt hc]
  have Cauchy_Schwarz_Ineq := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s hf hg ht
  unfold s f g r at Cauchy_Schwarz_Ineq; simp[Finset.sum_range_succ] at Cauchy_Schwarz_Ineq
  have : √ ((√a + √b + √c) ^ 2) = (√a + √b + √c) := Real.sqrt_sq (by positivity)
  rw[←this]; gcongr

lemma sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √ (a + b) ≤ √ a + √ b := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  ring_nf; field_simp
  positivity

lemma u_inf (hx : 0 ≤ x ∧ x ^ 2 ≤ 6) (hy : 0 ≤ y ∧ y ^ 2 ≤ 6) (hz : 0 ≤ z ∧ z ^ 2 ≤ 6)
                  (h : x ^ 2 + y ^ 2 + z ^ 2 = 10) :
            √ 6 + √ 2 ≤ u x y z := by
  unfold u at *
  wlog hxyz : z ^ 2 ≤ y ^ 2 ∧ y ^ 2 ≤ x ^ 2
  · push_neg at hxyz
    by_cases hzy : z ^ 2 ≤ y ^ 2
    · have hyx := hxyz hzy
      push_neg at this
      · by_cases hxz : x ^ 2 ≤ z ^ 2
        · have := this y z x hy hz hx (by linarith) ⟨hxz, hzy⟩
          linarith
        · push_neg at *
          have := this y x z hy hx hz (by linarith) ⟨by linarith, by linarith⟩
          linarith
    · by_cases hxy : x ^ 2 ≤ y ^ 2
      · have := this z y x hz hy hx (by linarith) ⟨by linarith, by linarith⟩
        linarith
      · by_cases hxz : x ^ 2 ≤ z ^ 2
        · have := this z x y hz hx hy (by linarith) ⟨by linarith, by linarith⟩
          linarith
        · have := this x z y hx hz hy (by linarith) ⟨by linarith, by linarith⟩
          linarith
  have : z ^ 2 ≤ 10 / 3 := by linarith
  have : √(6 - x ^ 2) + √(6 - y ^ 2) + √(6 - z ^ 2) ≥ √ 6 + √ 2 := by
    calc
    _≥ √ ((6 - x ^ 2) + (6 - y ^ 2)) + √ (6 - z ^ 2) := by
      have t2 : 6 - x ^ 2 ≥ 0 := by linarith
      have t1 : 6 - y ^ 2 ≥ 0 := by linarith
      linarith[sqrt_add_le_add_sqrt t2 t1]
    _= √ (2 + z ^ 2) + √ (6 - z ^ 2) := by
      have : (2 + z ^ 2) = ((6 - x ^ 2) + (6 - y ^ 2)) := by linarith
      simp; rw[this]
    _= √ (8 + 2 * √((2 + z ^ 2) * (6 - z ^ 2))) := by
      symm; apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      ring_nf; field_simp [hz.2]; ring_nf; simp
      rw[←Real.sqrt_mul (by linarith)]; ring_nf
    _≥ √ (8 + 2  * √ 12) := by
      gcongr
      ring_nf; field_simp
      nlinarith
    _= √ 6 + √ 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      ring_nf; field_simp; rw[add_comm, add_assoc]; congr
      · have : √ (6 * 2) = √ 6 * √ 2 := by apply Real.sqrt_mul (by norm_num) 2
        rw[←this]; norm_num
      · norm_num
  trivial

theorem GL2013BT3 (hx : 0 ≤ x ∧ x ^ 2 ≤ 6) (hy : 0 ≤ y ∧ y ^ 2 ≤ 6) (hz : 0 ≤ z ∧ z ^ 2 ≤ 6)
                  (h : x ^ 2 + y ^ 2 + z ^ 2 = 10) :
          √ 6 + √ 2 ≤ u x y z ∧ (∃ x₀ y₀ z₀ : ℝ, u x₀ y₀ z₀ = √ 6 + √ 2) ∧
          u x y z ≤ 2 * √ 6 ∧ ∃ x₀ y₀ z₀ : ℝ, u x₀ y₀ z₀ = 2 * √ 6 := by
  constructor
  · apply u_inf x y z hx hy hz h
  · constructor
    · use √ 6, 2, 0
      unfold u
      norm_num; linarith
    · constructor
      · unfold u
        have t1 : 6 - x ^ 2 ≥ 0 := by linarith
        have t2 : 6 - y ^ 2 ≥ 0 := by linarith
        have t3 : 6 - z ^ 2 ≥ 0 := by linarith
        have := CS_ineq t1 t2 t3
        have k1 : 6 - x ^ 2 + (6 - y ^ 2) + (6 - z ^ 2) = 8 := by linarith
        have k2 : √(3 * 8) = 2 * √6 := by apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr; ring; norm_num
        rwa[k1, k2] at this
      · use √ 30 / 3, √ 30 / 3, √ 30 / 3
        unfold u
        rw[div_pow]; norm_num; field_simp
        ring_nf;
        have : √ 8 * 3 = √ 72 := by symm; apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr; ring; norm_num
        have : √ 6 * √ 3 * 2 = √ 72 := by symm; apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr; ring; norm_num
        rwa[this]


end section
