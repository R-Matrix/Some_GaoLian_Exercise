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