## Theorem (USLLN, C)
Let $X_1, \ldots, X_n, \ldots$ be i.i.d. sample from $P$ on the space $\mathcal{X}$. Let $U(x,\theta)$ be a measurable function on $\mathcal{X} \times \Theta$. Suppose
1. $U(x,\theta)$ is continuous in $\theta$ for any fixed $x$,
2. for each $\theta$, $\mu(\theta) = \mathbb{E}U(X,\theta)$ is finite,
3. $\Theta$ is compact,
4. there exists a function $M(x)$ such that $\mathbb{E}M(X) < \infty$ and $|U(x,\theta)| \leq M(x)$ for all $x$ and $\theta$.

Then
$$P\left\{\lim_{n \to \infty} \sup_{\theta \in \Theta} \left|\frac{1}{n} \sum_{j=1}^n U(X_j, \theta) - \mu(\theta)\right| = 0\right\} = 1$$

### Proof
• By the continuity of $U(x, \cdot)$, its boundedness by $M(x)$, and DCT, $\mu(\theta)$ is continuous.
W.L.O.G., assume $\mu(\theta) \equiv 0$; otherwise consider $\tilde{U}(x,\theta) = U(x,\theta) - \mu(\theta)$

• Let 
$$\varphi(x, \theta, \rho) = \sup_{\|\theta' - \theta\| < \rho} U(x, \theta')$$

– $\varphi$ is measurable, bounded by $M$ and $\varphi(x, \theta, \rho) \to U(x,\theta)$ as $\rho \to 0$

• Fixed $\varepsilon > 0$. For each $\theta$, find $\rho_\theta > 0$ so that $\mathbb{E}\varphi(x, \theta, \rho_\theta) < \varepsilon$.
– By DCT, $\mathbb{E}\varphi(X, \theta, \rho) \to \mathbb{E}U(X,\theta) = \mu(\theta) = 0$, as $\rho \to 0$

• Note that the collection of $B(\theta, \rho_\theta) = \{\theta' : |\theta - \theta'| < \rho_\theta\}$ for all $\theta$ covers $\Theta$.
By the compactness of $\Theta$, there exists a finite sub-cover, say, $\Theta \subset \bigcup_{j=1}^m B(\theta_j, \rho_{\theta_j})$

• For each $\theta \in \Theta$, there exists an index $j$ such that $\theta \in B(\theta_j, \rho_{\theta_j})$ and $U(x,\theta) \leq \varphi(x, \theta_j, \rho_{\theta_j})$ for all $x$.

• So
$$\sup_{\theta \in \Theta} \frac{1}{n} \sum_{i=1}^n U(X_i, \theta) \leq \max_{1 \leq j \leq m} \frac{1}{n} \sum_{i=1}^n \varphi(X_i, \theta_j, \rho_{\theta_j})$$

• Apply SLLN to $\sum_{i=1}^n \varphi(X_i, \theta_j, \rho_{\theta_j})$ for each $j = 1, \ldots, m$, and use the continuity of max, we have
$$\lim_n \max_{1 \leq j \leq m} \frac{1}{n} \sum_{i=1}^n \varphi(X_i, \theta_j, \rho_{\theta_j}) = \max_{1 \leq j \leq m} \mathbb{E}\varphi(X, \theta_j, \rho_{\theta_j}) < \varepsilon, \quad \text{a.s.}$$

• Therefore $\limsup_n \sup_{\theta \in \Theta} \frac{1}{n} \sum_{i=1}^n U(X_i, \theta) < \varepsilon$, a.s. and thus,
$$\limsup_n \sup_{\theta \in \Theta} \frac{1}{n} \sum_{i=1}^n U(X_i, \theta) \leq 0, \quad \text{a.s.}$$

• Apply the same argument to $-U(x,\theta)$, we can conclude
$$\limsup_n \sup_{\theta \in \Theta} \frac{1}{n} \sum_{i=1}^n (-U)(X_i, \theta) \leq 0, \quad \text{a.s.}$$

• Note that $0 \leq \sup_\theta |g(\theta)| = \max\{\sup_\theta g(\theta), \sup_\theta [-g(\theta)]\}$.

## Definition (Kullback-Leibler Information)
The limit of the log-likelihood ratio is $-\mathbb{E}_{\theta_0} \log \frac{f(X|\theta_0)}{f(X|\theta)}$.

Define the **Kullback-Leibler (KL) information number** as
$$K(f_0, f_1) = \mathbb{E}_0 \log \frac{f_0(X)}{f_1(X)} = \int \log \left(\frac{f_0(x)}{f_1(x)}\right) f_0(x) d\nu(x)$$

When $f$ is indexed by $\theta$, we may also write $K(\theta_0, \theta_1)$ for short.

## Theorem (Shannon-Kolmogorov Information Inequality)
$K(f_0, f_1) \geq 0$ with equality if and only if $f_1(\omega) = f_0(\omega)$ $\nu$-a.e.