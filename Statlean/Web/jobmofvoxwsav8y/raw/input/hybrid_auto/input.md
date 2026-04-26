If $Z$ is not of full rank, then there are infinitely many LSE’s of $\beta$ . It can be shown (exercise) that any LSE of $\beta$ is of the form

$$
\hat {\beta} = \left(Z ^ {\tau} Z\right) ^ {-} Z ^ {\tau} X, \tag {3.29}
$$

where $( Z ^ { \tau } Z ) ^ { - }$ is called a generalized inverse of $Z ^ { \tau } Z$ and satisfies

$$
Z ^ {\tau} Z (Z ^ {\tau} Z) ^ {-} Z ^ {\tau} Z = Z ^ {\tau} Z.
$$

Generalized inverse matrices are not unique unless $Z$ is of full rank, in which case $( Z ^ { \tau } Z ) ^ { - } = ( Z ^ { \tau } Z ) ^ { - 1 }$ and (3.29) reduces to (3.28).

To study properties of LSE’s of $\beta$ , we need some assumptions on the distribution of $X$ . Since $Z _ { i }$ ’s are nonrandom, assumptions on the distribution of $X$ can be expressed in terms of assumptions on the distribution of $\varepsilon$ . Several commonly adopted assumptions are stated as follows.

Assumption A1: $\varepsilon$ is distributed as $N _ { n } ( 0 , \sigma ^ { 2 } I _ { n } )$ with an unknown $\sigma ^ { 2 } > 0$ .

Assumption A2: $E ( \varepsilon ) = 0$ and $\mathrm { V a r } ( \varepsilon ) = \sigma ^ { 2 } I _ { n }$ with an unknown $\sigma ^ { 2 } > 0$ .

Assumption A3: $E ( \varepsilon ) = 0$ and $\mathrm { V a r } ( \varepsilon )$ is an unknown matrix.

Assumption A1 is the strongest and implies a parametric model. We may assume a slightly more general assumption that $\varepsilon$ has the $N _ { n } ( 0 , \sigma ^ { 2 } D )$ distribution with unknown $\sigma ^ { 2 }$ but a known positive definite matrix $D$ . Let $D ^ { - 1 / 2 }$ be the inverse of the square root matrix of $D$ . Then model (3.25) with assumption A1 holds if we replace $X$ , $Z$ , and $\varepsilon$ by the transformed variables $\ddot { X } = D ^ { - 1 / 2 } X$ , $\ddot { Z } = D ^ { - 1 / 2 } Z$ , and $\tilde { \varepsilon } = D ^ { - 1 / 2 } \varepsilon$ , respectively. A similar conclusion can be made for assumption A2.

Under assumption A1, the distribution of $X$ is $N _ { n } ( Z \beta , \sigma ^ { 2 } I _ { n } )$ , which is in an exponential family $\mathcal { P }$ with parameter $\theta = ( \beta , \sigma ^ { 2 } ) \in \mathcal { R } ^ { p } \times ( 0 , \infty )$ . However, if the matrix $Z$ is not of full rank, then $\mathcal { P }$ is not identifiable (see 2.1.2), since $Z \beta _ { 1 } = Z \beta _ { 2 }$ does not imply $\beta _ { 1 } = \beta _ { 2 }$ .

Suppose that the rank of $Z$ is $r \le p$ . Then there is an $n \times r$ submatrix $Z _ { * }$ of $Z$ such that

$$
Z = Z _ {*} Q \tag {3.30}
$$

and $Z _ { * }$ is of rank $r$ , where $Q$ is a fixed $r \times p$ matrix. Then

$$
Z \beta = Z _ {*} Q \beta
$$

and $\mathcal { P }$ is identifiable if we consider the reparameterization $\bar { \beta } = Q \beta$ . Note that the new parameter $\tilde { \beta }$ is in a subspace of $\mathcal { R } ^ { p }$ with dimension $r$ .

In many applications, we are interested in estimating some linear functions of $\beta$ , i.e., $\vartheta = l ^ { \tau } \beta$ for some $l \in \mathcal { R } ^ { p }$ . From the previous discussion, however, estimation of $l ^ { \tau } \beta$ is meaningless unless $l = Q ^ { \tau } c$ for some $c \in \mathcal { R } ^ { r }$ so that

$$
l ^ {\tau} \beta = c ^ {\tau} Q \beta = c ^ {\tau} \tilde {\beta}.
$$

The following result shows that $l ^ { \tau } \beta$ is estimable if ${ \mathit { l } } = Q ^ { \tau } c$ , which is also necessary for $l ^ { \tau } \beta$ to be estimable under assumption A1.

Theorem 3.6. Assume model (3.25) with assumption A3.

(i) A necessary and sufficient condition for $l ~ \in ~ \mathcal { R } ^ { p }$ being $Q ^ { \tau } c$ for some $c \in \mathcal { R } ^ { r }$ is $l \in \mathcal { R } ( Z ) = \mathcal { R } ( Z ^ { \tau } Z )$ , where $Q$ is given by (3.30) and $\mathcal { R } ( A )$ is the smallest linear subspace containing all rows of $A$ .

(ii) If $l \in \mathcal { R } ( Z )$ , then the LSE $l ^ { \tau } \hat { \beta }$ is unique and unbiased for $l ^ { \tau } \beta$ .

(iii) If $l \not \in \mathcal { R } ( Z )$ and assumption A1 holds, then $l ^ { \tau } \beta$ is not estimable.

Proof. (i) Note that $a \in { \mathcal { R } } ( A )$ if and only if $a = A ^ { \tau } b$ for some vector $b$ . If $l = Q ^ { \prime } c$ , then

$$
l = Q ^ {\tau} c = Q ^ {\tau} Z _ {*} ^ {\tau} Z _ {*} (Z _ {*} ^ {\tau} Z _ {*}) ^ {- 1} c = Z ^ {\tau} [ Z _ {*} (Z _ {*} ^ {\tau} Z _ {*}) ^ {- 1} c ].
$$

Hence $l \in \mathcal { R } ( Z )$ . If $l \in \mathcal { R } ( Z )$ , then $l = Z ^ { \tau } \zeta$ for some $\zeta$ and

$$
l = \left(Z _ {*} Q\right) ^ {\tau} \zeta = Q ^ {\tau} c
$$

with $c = Z _ { * } ^ { \tau } \zeta$ .

(ii) If $l \in \mathcal { R } ( Z ) = \mathcal { R } ( Z ^ { \tau } Z )$ , then $l = Z ^ { \tau } Z \zeta$ for some $\zeta$ and by (3.29),

$$
\begin{array}{l} E \left(l ^ {\tau} \hat {\beta}\right) = E \left[ l ^ {\tau} \left(Z ^ {\tau} Z\right) ^ {-} Z ^ {\tau} X \right] \\ = \zeta^ {\tau} Z ^ {\tau} Z \left(Z ^ {\tau} Z\right) ^ {-} Z ^ {\tau} Z \beta \\ = \zeta^ {\tau} Z ^ {\tau} Z \beta \\ = l ^ {\tau} \beta . \\ \end{array}
$$

If $\beta$ is any other LSE of $\beta$ , then, by (3.27),

$$
l ^ {\tau} \hat {\beta} - l ^ {\tau} \bar {\beta} = \zeta^ {\tau} (Z ^ {\tau} Z) (\hat {\beta} - \bar {\beta}) = \zeta^ {\tau} (Z ^ {\tau} X - Z ^ {\tau} X) = 0.
$$

(iii) Under assumption A1, if there is an estimator $h ( X , Z )$ unbiased for $l ^ { \tau } \beta$ , then

$$
l ^ {\tau} \beta = \int_ {\mathcal {R} ^ {n}} h (x, Z) (2 \pi) ^ {- n / 2} \sigma^ {- n} \exp \left\{- \frac {1}{2 \sigma^ {2}} \| x - Z \beta \| ^ {2} \right\} d x.
$$

Differentiating w.r.t. $\beta$ and applying Theorem 2.1 lead to

$$
l = Z ^ {\tau} \int_ {\mathcal {R} ^ {n}} h (x, Z) (2 \pi) ^ {- n / 2} \sigma^ {- n - 2} (x - Z \beta) \exp \left\{- \frac {1}{2 \sigma^ {2}} \| x - Z \beta \| ^ {2} \right\} d x,
$$

which implies $l \in \mathcal { R } ( Z )$ .

Theorem 3.6 shows that LSE’s are unbiased for estimable parameters $l ^ { \tau } \beta$ . If $Z$ is of full rank, then $\mathcal { R } ( Z ) = \mathcal { R } ^ { p }$ and, therefore, $l ^ { \tau } \beta$ is estimable for any $l \in \mathcal { R } ^ { p }$ .