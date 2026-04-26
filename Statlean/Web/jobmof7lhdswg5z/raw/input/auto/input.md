Theorem 3.5. Let $U _ { n }$ be given by (3.11) with $E [ h ( X _ { 1 } , . . . , X _ { m } ) ] ^ { 2 } < \infty$ . (i) If $\zeta _ { 1 } > 0$ , then

$$
\sqrt { n } [ U _ { n } - E ( U _ { n } ) ] \to _ { d } N ( 0 , m ^ { 2 } \zeta _ { 1 } ) .
$$

(ii) If $\zeta _ { 1 } = 0$ but $\zeta _ { 2 } > 0$ , then

$$
n [ U _ { n } - E ( U _ { n } ) ] \to _ { d } { \frac { m ( m - 1 ) } { 2 } } \sum _ { j = 1 } ^ { \infty } \lambda _ { j } ( \chi _ { 1 j } ^ { 2 } - 1 ) ,
$$

where $\chi _ { 1 j } ^ { 2 }$ ’s are i.i.d. random variables having the chi-square distribution $\chi _ { 1 } ^ { 2 }$ and $\lambda _ { j }$ 1j ’s are some constants (which may depend on $P$ ) satisfying $\textstyle \sum _ { j = 1 } ^ { \infty } \lambda _ { j } ^ { 2 } =$ $\zeta _ { 2 }$ . ■

We have actually proved Theorem 3.5(i). A proof for Theorem 3.5(ii) is given in Serfling (1980, 5.5.2). One may derive results for the cases where $\zeta _ { 2 } = 0$ , but the case of either $\zeta _ { 1 } > 0$ or $\zeta _ { 2 } > 0$ is the most interesting case in applications.

If $\zeta _ { 1 } > 0$ , it follows from Theorem 3.5(i) and Corollary 3.2(iii) that $\mathrm { a m s e } _ { U _ { n } } ( P ) ~ = ~ m ^ { 2 } \zeta _ { 1 } / n ~ = ~ \mathrm { V a r } ( U _ { n } ) + { \cal O } ( n ^ { - 2 } )$ . By Proposition 2.4(ii), $\{ n [ U _ { n } - E ( U _ { n } ) ] ^ { 2 } \}$ is uniformly integrable.

If $\zeta _ { 1 } = 0$ but $\zeta _ { 2 } > 0$ , it follows from Theorem 3.5(ii) that $\mathrm { a m s e } _ { U _ { n } } ( P ) =$ $E Y ^ { 2 } / n ^ { 2 }$ , where $Y$ denotes the random variable on the right-hand side of (3.21). The following result provides the value of $E Y ^ { 2 }$ .

Lemma 3.2. Let $Y$ be the random variable on the right-hand side of (3.21). Then EY 2 = $\begin{array} { r } { E Y ^ { 2 } = \frac { m ^ { 2 } ( m - 1 ) ^ { 2 } } { 2 } \zeta _ { 2 } } \end{array}$ .   
Proof. Define

$$
Y _ { k } = \frac { m ( m - 1 ) } { 2 } \sum _ { j = 1 } ^ { k } \lambda _ { j } ( \chi _ { 1 j } ^ { 2 } - 1 ) , \quad k = 1 , 2 , \ldots
$$

It can be shown (exercise) that $\{ Y _ { k } ^ { 2 } \}$ is uniformly integrable. Since $Y _ { k }  _ { d } Y$ as $k  \infty$ , $\begin{array} { r } { \operatorname* { l i m } _ { k \to \infty } E Y _ { k } ^ { 2 } = E Y ^ { 2 } } \end{array}$ (Theorem 1.8(viii)). Since $\chi _ { 1 j } ^ { 2 }$ ’s are independent chi-square random variables with $E \chi _ { 1 j } ^ { 2 } = 1$ and $\mathrm { V a r } ( \chi _ { 1 j } ^ { 2 } ) = 2$ , $E Y _ { k } = 0$ for any $k$ and

$$
\begin{array} { l } { { E Y _ { k } ^ { 2 } = \displaystyle \frac { m ^ { 2 } ( m - 1 ) ^ { 2 } } { 4 } \sum _ { j = 1 } ^ { k } \lambda _ { j } ^ { 2 } \mathrm { V a r } ( \chi _ { 1 j } ^ { 2 } ) } } \\ { { \mathrm { } } } \\ { { \mathrm { } = \displaystyle \frac { m ^ { 2 } ( m - 1 ) ^ { 2 } } { 4 } \left( 2 \sum _ { j = 1 } ^ { k } \lambda _ { j } ^ { 2 } \right) } } \\ { { \mathrm { } } } \\ { { \mathrm { } \longrightarrow \displaystyle \frac { m ^ { 2 } ( m - 1 ) ^ { 2 } } { 2 } \zeta _ { 2 } . ~ } } \end{array}
$$