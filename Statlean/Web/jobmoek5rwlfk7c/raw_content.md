# 3.2.2 Variances of U-statistics

If $E [ h ( X _ { 1 } , . . . , X _ { m } ) ] ^ { 2 } < \infty$ , then the variance of $U _ { n }$ in (3.11) with kernel $h$ has an explicit form. To derive ${ \mathrm { V a r } } ( U _ { n } )$ , we need some notation. For $k = 1 , . . . , m$ , let

$$
\begin{array}{l} h _ {k} \left(x _ {1}, \dots , x _ {k}\right) = E \left[ h \left(X _ {1}, \dots , X _ {m}\right) \mid X _ {1} = x _ {1}, \dots , X _ {k} = x _ {k} \right] \\ = E [ h (x _ {1}, \dots , x _ {k}, X _ {k + 1}, \dots , X _ {m}) ]. \\ \end{array}
$$

Note that $h _ { m } = h$ . It can be shown that

$$
h _ {k} \left(x _ {1}, \dots , x _ {k}\right) = E \left[ h _ {k + 1} \left(x _ {1}, \dots , x _ {k}, X _ {k + 1}\right) \right]. \tag {3.14}
$$

Define

$$
\tilde {h} _ {k} = h _ {k} - E [ h \left(X _ {1}, \dots , X _ {m}\right) ], \tag {3.15}
$$

$k = 1 , . . . , m$ , and $\ddot { h } = \ddot { h } _ { m }$ . Then, for any $U _ { n }$ defined by (3.11),

$$
U _ {n} - E \left(U _ {n}\right) = \binom {n} {m} ^ {- 1} \sum_ {c} \tilde {h} \left(X _ {i _ {1}}, \dots , X _ {i _ {m}}\right). \tag {3.16}
$$

Theorem 3.4 (Hoeffding’s theorem). For a U-statistic $U _ { n }$ given by (3.11) with $E [ h ( X _ { 1 } , . . . , X _ { m } ) ] ^ { 2 } < \infty$ ,

$$
\operatorname {V a r} (U _ {n}) = \binom {n} {m} ^ {- 1} \sum_ {k = 1} ^ {m} \binom {m} {k} \binom {n - m} {m - k} \zeta_ {k},
$$

where

$$
\zeta_ {k} = \operatorname {V a r} \left(h _ {k} \left(X _ {1}, \dots , X _ {k}\right)\right).
$$

Proof. Consider two sets $\{ i _ { 1 } , . . . , i _ { m } \}$ and $\{ j _ { 1 } , . . . , j _ { m } \}$ of $m$ distinct integers from $\{ 1 , . . . , n \}$ with exactly $k$ integers in common. The number of distinct choices of two such sets is $\binom { n } { m } \left( { m \atop k } \right) \left( { n { - } m \atop m { - } k } \right)$ . By the symmetry of $\ddot { h } _ { m }$ and independence of $X _ { 1 } , . . . , X _ { n }$ ,

$$
E \left[ \tilde {h} \left(X _ {i _ {1}}, \dots , X _ {i _ {m}}\right) \tilde {h} \left(X _ {j _ {1}}, \dots , X _ {j _ {m}}\right) \right] = \zeta_ {k} \tag {3.17}
$$

for $k = 1 , . . . , m$ (exercise). Then, by (3.16),

$$
\begin{array}{l} \operatorname {V a r} (U _ {n}) = \binom {n} {m} ^ {- 2} \sum_ {c} \sum_ {c} E [ \tilde {h} (X _ {i _ {1}}, \dots , X _ {i _ {m}}) \tilde {h} (X _ {j _ {1}}, \dots , X _ {j _ {m}}) ] \\ = \binom {n} {m} ^ {- 2} \sum_ {k = 1} ^ {m} \binom {n} {m} \binom {m} {k} \binom {n - m} {m - k} \zeta_ {k}. \\ \end{array}
$$

This proves the result.