# 2005 年高中联赛 $\cdot$ 二试

## 第三题

设整数 $n \ge 3$ , 正实数 $\alpha_1, \alpha_2, \cdots , \alpha_n$ 满足 $a_k \le 1, k = 1, 2, \cdots n$. 对 $1 \le k \le n$, 
记$A_k = \dfrac{a_1 + a_2 + \cdots + a_n}{k} $.

求证 : 
$$\left| \sum_{k=1}^n a_k- \sum _{k = 1} ^ n A_k  \right| < \frac {n-1} 2.$$

---

## 答案

由三角不等式,
$$\left| \sum_{k=1}^n a_k - \sum_{k=1}^n A_k \right| = \left| nA_n - \sum _{k = 1} ^ n A_k  \right| = \left|\sum _{k=1}^{n-1}(A_n - A_k) \right|\le \sum_{k=1}^{n-1} \left|A_n - A_k \right|.$$

对 $1 \le k \le n-1 $, 
$$A_n - A_k = \frac 1n \sum_{i=1}^n a_i - \frac 1k \sum_{i =1}^k a_i 
= \frac 1n \sum _{i = k + 1}^n a_i - \left(\frac 1k - \frac 1n\right)\sum_{i=1}^k a_i
$$

由 $0 < a_i \le 1$ 知,

$$0 < \sum_{i = 1}^k a_i \le k, \qquad 0 < \sum_{i=k+1}^n a_i \le n - k$$

所以 
$$\frac 1n\sum_{i=k+1}^n a_i - \left(\frac 1k - \frac 1n \right)\sum_{i=1}^k a_i < \frac 1n (n-k) = 1-\frac kn $$

$$\frac 1n\sum_{i=k+1}^n a_i - \left(\frac 1k - \frac 1n \right)\sum_{i=1}^k a_i > - \left(\frac 1k - \frac 1n\right) k = - \left(1- \frac kn\right) $$

从而 $|A_n - A_k | < 1 - \dfrac kn .$

这样,

$$\left| \sum_{k=1}^n a_k - \sum_{k=1}^n A_k \right| \le \sum_{k=1}^{n-1} \left|A_n - A_k \right| < \sum_{k = 1}^{n-1} \left(1 - \dfrac kn \right) = \frac {n-1}{2}.\quad \square$$