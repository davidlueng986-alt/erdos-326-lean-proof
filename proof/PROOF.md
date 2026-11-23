# Complete Proof of JSP-000272 (Erdős Problem #326)

- **Problem ID:** `JSP-000272` ([Justin Sun Prize Catalog](https://github.com/TheJustinSunPrize/awards/blob/10e0ab6e7503b6db769029d7d68cc4ca42c011d7/problems/catalog-0201-0300.md#JSP-000272)) / [Erdős Problem #326](https://erdosproblemaday.com/problem/326) (listed as **open** on the official site as of November 2026)
- **Statement:** Does there exist a set $A = \{a_1 < a_2 < \cdots\} \subset \mathbb{N}$ which is a minimal asymptotic additive basis of order $2$ (every sufficiently large integer is the sum of two elements of $A$, and no proper subset of $A$ has this property) such that $\lim_{k \to \infty} \frac{a_k}{k^2} = c$ for some $c \neq 0$? (Erdős and Graham 1980 conjectured a negative answer.)
- **Resolution:** **YES** (refuting the Erdős–Graham conjecture). We construct an explicit minimal asymptotic basis $C' = \{c'_1 < c'_2 < \cdots\} \subset \mathbb{N}_{>0}$ of order $2$ with $C' + C' = \mathbb{N}_{\ge 2}$ and $\lim_{k \to \infty} c'_k / k^2 = \frac{1}{10000} > 0$.

---

## Main Theorem

**Theorem.** *There exists an infinite set $C' = \{c'_1 < c'_2 < \cdots\} \subset \mathbb{N}_{>0}$ such that:*
1. *$C' + C' = \mathbb{N}_{\ge 2}$ (in particular, $C'$ is an asymptotic additive basis of order $2$);*
2. *for every $x \in C'$, the set $C' \setminus \{x\}$ is not an asymptotic additive basis of order $2$ ($C'$ is minimal);*
3. *$\lim_{k \to \infty} \frac{c'_k}{k^2} = \frac{1}{10000} > 0$ (in fact $c'_k = \frac{1}{10000} k^2 + O(k)$).*

---

## Proof

### Step 1: Two Coprime Prime-Step Cassels Bases $A^{(1)}, A^{(2)}$

Set $q_1^{(1)} = q_1^{(2)} = 1$. For each $i \ge 2$, by Bertrand's Postulate choose primes
$$q_i^{(1)} \in \bigl(3 \cdot 4^{i-1},\, 6 \cdot 4^{i-1}\bigr], \qquad q_i^{(2)} \in \bigl(6 \cdot 4^{i-1},\, 12 \cdot 4^{i-1}\bigr].$$
Because $3 \cdot 4^{i-1} < 6 \cdot 4^{i-1} < 12 \cdot 4^{i-1} = 3 \cdot 4^i < q_{i+1}^{(1)}$, all primes $\{q_i^{(s)} : i \ge 2,\ s \in \{1,2\}\}$ are pairwise distinct. Consequently:
- $\gcd(q_{i-1}^{(s)}, q_i^{(s)}) = \gcd(q_{i-1}^{(s)}, q_{i+1}^{(s)}) = 1$ for all $i \ge 2$ and $s \in \{1,2\}$;
- $\gcd(q_i^{(1)}, q_j^{(2)}) = 1$ for **all** $i, j \ge 1$.

For $s \in \{1, 2\}$ and $i \ge 1$, define
$$m_i^{(s)} := q_{i+1}^{(s)} + q_{i+2}^{(s)}, \qquad Q_1^{(s)} := 0, \qquad Q_k^{(s)} := \sum_{i=1}^{k-1} m_i^{(s)} q_i^{(s)} \quad (k \ge 2),$$
$$A_k^{(s)} := \bigl\{Q_k^{(s)} + t q_k^{(s)} : 0 \le t \le m_k^{(s)}\bigr\}, \qquad A^{(s)} := \bigcup_{k=1}^\infty A_k^{(s)}, \qquad A := A^{(1)} \cup A^{(2)}.$$

**Verification of Cassels's Theorem** ([Nathanson, *Cassels Bases*, Thm. 6](http://www.theoryofnumbers.com/melnathanson/pdfs/nath2010-138.pdf)):
Writing $c_s = 3s \in \{3, 6\}$, for $i \ge 3$ we have
$$m_{i+1}^{(s)} q_{i+1}^{(s)} > (c_s 4^i)(c_s 4^{i+1} + c_s 4^{i+2}) = 20 c_s^2 \cdot 16^i,$$
$$m_i^{(s)} q_i^{(s)} + m_{i-1}^{(s)} q_{i-1}^{(s)} \le (2c_s 4^{i-1})(2c_s 4^i + 2c_s 4^{i+1}) + (2c_s 4^{i-2})(2c_s 4^{i-1} + 2c_s 4^i) = \frac{85}{16} c_s^2 \cdot 16^i < 20 c_s^2 \cdot 16^i.$$
For $i = 2$, $m_3^{(1)} q_3^{(1)} > 48(192+768) = 46080 > 11640 \ge m_2^{(1)} q_2^{(1)} + m_1^{(1)} q_1^{(1)}$, and similarly for $s = 2$ ($184320 > 46320$).

**Self-contained proof that $[2Q_k^{(s)}, 2Q_{k+1}^{(s)}] \subseteq A_{k-1}^{(s)} + (A_k^{(s)} \cup A_{k+1}^{(s)})$ for $k \ge 2$:**
Drop superscripts $(s)$ and let $n \in [2Q_k, 2Q_{k+1}]$.
- *Subinterval 1:* $n \in [2Q_k,\, Q_{k-1} + Q_{k+1} + (q_{k+1}+1)q_{k-1}]$. Since $\gcd(q_{k-1}, q_k) = 1$, choose the unique $t \in [m_{k-1} - q_k + 1,\, m_{k-1}] = [q_{k+1}+1,\, q_k + q_{k+1}]$ with $Q_{k-1} + Q_k + t q_{k-1} \equiv n \pmod{q_k}$. Then $u := \frac{n - (Q_{k-1} + Q_k + t q_{k-1})}{q_k}$ satisfies $u \ge \frac{(m_{k-1}-t)q_{k-1}}{q_k} \ge 0$ and $u \le \frac{Q_{k+1} - Q_k + (q_{k+1}+1 - t)q_{k-1}}{q_k} \le m_k$, so $n \in A_{k-1} + A_k$.
- *Subinterval 2:* $n \in [Q_{k-1} + Q_{k+1} + (q_{k+1}-1)q_{k-1},\, 2Q_{k+1}]$. Since $\gcd(q_{k-1}, q_{k+1}) = 1$, choose the unique $t \in [0, q_{k+1}-1] \subset [0, m_{k-1}]$ with $Q_{k-1} + Q_{k+1} + t q_{k-1} \equiv n \pmod{q_{k+1}}$. Then $v := \frac{n - (Q_{k-1} + Q_{k+1} + t q_{k-1})}{q_{k+1}}$ satisfies $v \ge 0$ and $v q_{k+1} \le 2Q_{k+1} - Q_{k-1} - Q_{k+1} = m_{k-1} q_{k-1} + m_k q_k \le m_{k+1} q_{k+1}$, so $0 \le v \le m_{k+1}$ and $n \in A_{k-1} + A_{k+1}$.

Since the two subintervals overlap and $A_1^{(s)} + A_1^{(s)} = [0, 2Q_2^{(s)}]$, each $A^{(s)}$ is an exact basis of order $2$ for $\mathbb{N}_0$, and every $n \in \mathbb{N}_0$ has a fixed **canonical representation** $n = u^{(s)}(n) + v^{(s)}(n)$ with block indices differing by at most $2$.

---

### Step 2: Explicit Scale and Gap Bounds

For every $k \ge 3$ and $s \in \{1, 2\}$ ($c_s = 3s$):
$$\frac{5 c_s^2}{64} \cdot 16^k < Q_k^{(s)} < \frac{c_s^2}{3} \cdot 16^k.$$
Hence for any consecutive elements $a < a'$ of $A^{(s)}$ with $a \ge Q_3^{(s)}$, if $a \in A_k^{(s)}$ ($k \ge 3$) then $a \le Q_{k+1}^{(s)} < \frac{16 c_s^2}{3} \cdot 16^k$ while $a' - a \ge q_k^{(s)} > \frac{c_s}{4} 4^k$, giving
$$a' - a > \frac{\sqrt{3}}{16}\sqrt{a} > \frac{1}{10}\sqrt{a}.$$

---

### Step 3: Quadratic Bins and Running-Count Rule

Set $b_m := \lfloor m^2 / 10000 \rfloor$, $I_m := (b_m, b_{m+1}]$, $L_m := b_{m+1} - b_m$, and $m_0 := 10^5$ (so $b_{m_0} = 10^6 > Q_3^{(2)} > Q_3^{(1)}$). For all $m \ge m_0$:
$$\frac{m}{6000} < L_m < \frac{m}{4000} \le \frac{1}{39}\sqrt{b_m}.$$
Because consecutive elements of $A^{(s)}$ above $b_{m_0}$ have gap $> \frac{1}{10}\sqrt{b_m} > 3.9 L_m$, **every $3$ consecutive bins $I_m, I_{m+1}, I_{m+2}$ ($m \ge m_0$) contain at most $1$ element of $A^{(1)}$ and at most $1$ element of $A^{(2)}$**.

Initialize $C^{(0)} \subseteq [0, b_{m_0}]$ as $A \cap [0, b_{m_0}]$ plus $m_0 - |A \cap [0, b_{m_0}]|$ distinct integers in $[0, b_{m_0}]$ so that $|C^{(0)} \cap [0, b_{m_0}]| = m_0$ and $0 \in A^{(1)} \subset C^{(0)}$.

For any bin $I_m$ ($m \ge m_0$) and optional forbidden set $F_{\text{forb}}$, the **bin-filling rule** adds $\max(0,\ (m+1) - |C \cap [0, b_{m+1}]|)$ distinct integers from $I_m \setminus (C \cup F_{\text{forb}})$ to $C$.

---

### Step 4: Inductive Stage-by-Stage Construction

Use a standard dovetailing enumeration so that every element $x \in C$ is selected as the target witness $x_r \in C^{(r-1)}$ at infinitely many stages $r = 1, 2, \dots$.

Before stage $r$, we have $C^{(r-1)} \subseteq [0, Y_{r-1}]$ ($Y_0 := b_{m_0}$). Choose a bin boundary $2X_r = b_{m_1}$ sufficiently large that:
- $X_r > \max\bigl(Y_{r-1},\, 10 x_r,\, (100\Delta_0 + E'\Delta_0)^2\bigr)$ (with explicit absolute constants $K_0, M_{\max}, E', \Delta_0$ below, independent of $r$);
- $L_m \ge 4(K_0 + 200\sqrt{L_m} + E' + 2)$ for all $b_m \ge X_r$;
- after normal bin-filling on $(Y_{r-1}, 2X_r]$ using $A$ and $F_{\text{forb}} = \emptyset$, the excess has decayed so $|C \cap [0, 2X_r]| \in \{m_1, m_1 + 1\}$.

Set $C_{\text{old}} := C \cap [0, 2X_r]$. Note $|C_{\text{old}}| \le 100\sqrt{2X_r} + 11$, independent of $M_{\max}$ and $E'$.

#### 4.1. Selecting an Odd Target $N_r \in [4X_r, 4.1 X_r]$ by Averaging
For odd $N \in [4X_r, 4.1 X_r]$, set
$$D_1(N) := A \cap (2X_r, N] \cap (N - C_{\text{old}}), \qquad D_2(N) := A \cap (N/2, N - 2X_r] \cap \bigl(N - (A \cap (2X_r, N/2])\bigr).$$
Since $\sum_N |D_1(N)| \le |A \cap (2X_r, 4.1 X_r]| \cdot |C_{\text{old}}| = O(X_r)$ and $\sum_N |D_2(N)| \le |A \cap (2X_r, 2.1 X_r]|^2 = O(X_r)$ over $\ge 0.04 X_r$ odd integers $N$, there exists an odd $N_r \in [4X_r, 4.1 X_r]$ with $|D_r| \le K_0$ for an explicit absolute constant $K_0$, where $D_r := D_1(N_r) \cup D_2(N_r)$.

#### 4.2. Filling $(2X_r, N_r]$ with Zero Representations of $N_r$
Place $(A \setminus D_r) \cap (2X_r, N_r]$ into $C$, then apply the bin-filling rule across bins intersecting $(2X_r, N_r]$:
- for $b_{m+1} \le \lfloor N_r/2 \rfloor$, set $F_{\text{forb}} := N_r - A$ (excludes $\le 2$ points per bin);
- for the unique bin $I_{m^*}$ straddling $\lfloor N_r/2 \rfloor$, place any needed filler in whichever half has length $\ge \lfloor L_{m^*}/2 \rfloor$ using the matching $F_{\text{forb}}$;
- for $b_m \ge \lfloor N_r/2 \rfloor$, set $F_{\text{forb}} := N_r - (C \cap [0, \lfloor N_r/2 \rfloor])$ (excludes $\le 100\sqrt{L_m} + E' + 2 \ll L_m/2$ points per bin).

Because $N_r$ is odd, no diagonal sum $2v = N_r$ exists, and every pair $u < v$ with $u + v = N_r$ is excluded by $D_1$, $D_2$, or $F_{\text{forb}}$. Hence $N_r \notin C + C$.

#### 4.3. Adding the Unique Witness $b_r := N_r - x_r$
Add $b_r := N_r - x_r$ to $C$. Since $b_r > 3.9 X_r > Y_{r-1} > N_{r-1} > \cdots > N_1$ and $N_r$ is odd, $\{x_r, b_r\}$ is now the **unique** unordered representation of $N_r$ in $C + C$, and no earlier $N_{r'}$ gains a representation.

#### 4.4. Uniform Constant Bound $|H_r| \le M_{\max}$ on Collateral Holes & Stage Disjointness
Any integer $n$ whose canonical representation in $A^{(s)}$ uses some $d \in D_r^{(s)} \subseteq (2X_r, N_r]$ has partner $x \in A_m^{(s)}$ with $m \le k + 2$ (where $Q_k^{(s)} \le d$), so $x \le Q_{k+3}^{(s)} < \frac{64}{15} \cdot 4096 \cdot Q_k^{(s)} < 18000 d$, whence
$$2X_r < n < 18001 N_r < 20000 N_r =: Y_r.$$
Because $X_{r} > Y_{r-1}$, the affected zones $(2X_j, Y_j)$ of distinct stages $j$ are **pairwise disjoint**: no integer $n$ can simultaneously lose its $A^{(1)}$-representation at one stage and its $A^{(2)}$-representation at a different stage.

Thus the set $H_r$ of integers $n \neq N_r$ losing both canonical representations at stage $r$ consists of solutions to $n = d_1 + x_1 = d_2 + x_2$ with $d_1 \in D_r^{(1)}$, $d_2 \in D_r^{(2)}$, $x_1 = Q_m^{(1)} + t_1 q_m^{(1)}$, $x_2 = Q_\ell^{(2)} + t_2 q_\ell^{(2)}$, and $|m - \ell| \le 6$ (since $d_1, d_2 \in (2X_r, 4.1 X_r]$ pins $k_1 - k_2 \le 2$). Because $\gcd(q_m^{(1)}, q_\ell^{(2)}) = 1$, $t_1$ is uniquely determined modulo $q_\ell^{(2)}$, yielding at most $\lfloor m_m^{(1)} / q_\ell^{(2)} \rfloor + 1 \le 5 \cdot 4^{m-\ell+1} + 1 \le 81921$ solutions per $(d_1, d_2, m, \ell)$. Summing over $\le K_0^2$ pairs $(d_1, d_2)$ and $\le 100$ block pairs gives
$$|H_r| \le M_{\max} := 100 \cdot 81921 \cdot K_0^2.$$

#### 4.5. Patching $H_r = \{n_1, \dots, n_M\}$ ($M \le M_{\max}$)
Set $E' := M_{\max} + 4$ and $\Delta_0 := \max((E'+1)^2,\ b_{m_0} + 1)$. Maintaining $C_{\text{cur}}$ (starting with $C$ on $[0, N_r]$ including $b_r$), for each $t = 1, \dots, M$:
- **Case A ($n_t > N_r$):** Add $w_t := n_t$. Then $0 + w_t = n_t \in C + C$, and $w_t > N_r > \cdots > N_1$ cannot represent $N_r$ or any earlier $N_{r'}$.
- **Case B ($2X_r < n_t < N_r$):** Set $\Delta := N_r - n_t \in [1, 2.1 X_r]$. Pick $a_t \in C_{\text{old}} \cap [0, X_r]$ with $a_t + \Delta \notin C_{\text{cur}}$, and add $w_t := n_t - a_t$. Then $a_t + w_t = n_t$, $w_t > X_r > Y_{r-1} > N_{r-1}$ (cannot hit any earlier $N_{r'}$), $2w_t \neq N_r$ ($N_r$ odd), and $w_t + u = N_r \iff u = a_t + \Delta \notin C_{\text{cur}}$. Existence of $a_t$:
  - *Subcase B1 ($\Delta \ge \Delta_0$):* Let $Y := \min(\Delta, X_r) \ge \Delta_0$. Since $\Delta - 1 \ge b_{m_0}$ and $\Delta + Y < 3.1 X_r < N_r$, the uniform bin count gives $100\sqrt{x} - 1 < |C_{\text{cur}} \cap [0, x]| < 100\sqrt{x} + E' + 1$ on $[b_{m_0}, N_r]$, so by concavity ($\sqrt{\Delta + Y} - \sqrt{\Delta} < 0.42\sqrt{Y}$),
    $$|C_{\text{old}} \cap [0, Y]| - |C_{\text{cur}} \cap [\Delta, \Delta + Y]| > 58\sqrt{Y} - E' - 3 > 0.$$
  - *Subcase B2 ($1 \le \Delta < \Delta_0$):* Every $w_s$ ($s < t$) and $b_r$ exceeds $X_r$, so $C_{\text{cur}} \cap [0, X_r] = C_{\text{old}} \cap [0, X_r]$. If $a + \Delta \in C_{\text{old}}$ for all $a \in C_{\text{old}} \cap [0, X_r - \Delta]$, then $0 \in C_{\text{old}}$ forces $\{j\Delta : 0 \le j \le \lfloor X_r/\Delta \rfloor\} \subseteq C_{\text{old}} \cap [0, X_r]$, giving $|C_{\text{old}} \cap [0, X_r]| > X_r / \Delta_0 > 100\sqrt{X_r} + E' + 1$, contradiction.

#### 4.6. Finalizing Stage $r$
Fill $(N_r, Y_r]$ using $A$ and the bin-filling rule (accounting for any $w_t \in (N_r, Y_r]$). Because $b_r$ and all $w_t$ exceed $X_r > Y_{r-1}$, $C^{(r)} \cap [0, Y_{r-1}] = C^{(r-1)}$. Set $C := \bigcup_{r=0}^\infty C^{(r)}$.

---

### Step 5: Verification & Positive-Integer Shift

1. **Basis of order $2$:** Every $n \in \mathbb{N}_0$ is covered by $A^{(1)} \setminus \bigcup D_r^{(1)}$, $A^{(2)} \setminus \bigcup D_r^{(2)}$, $x_r + b_r$ (if $n = N_r$), or $0 + w_t / a_t + w_t$ (if $n \in H_r$). Thus $C + C = \mathbb{N}_0$.
2. **Minimality:** Every $x \in C$ is chosen as $x_r$ at infinitely many stages $r$, each producing a target $N_r \to \infty$ whose unique representation in $C + C$ is $\{x_r, b_r\}$.
3. **Quadratic growth:** For all $m \ge m_0$, $m \le |C \cap [0, b_m]| \le m + M_{\max} + 3$ (the excess decays by at least $1$ every $3$ bins after $Y_r$), yielding $b_{k - M_{\max} - 4} < c_k \le b_k$ and $\lim_{k \to \infty} c_k / k^2 = \frac{1}{10000}$.
4. **Positive integers:** $C' := \{c + 1 : c \in C\} \subset \mathbb{N}_{>0}$ satisfies $C' + C' = \mathbb{N}_{\ge 2}$, preserves minimality via witnesses $N_r + 2$, and satisfies $\lim_{k \to \infty} c'_k / k^2 = \frac{1}{10000} > 0$. $\blacksquare$
