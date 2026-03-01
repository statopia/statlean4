ST6101: Advanced Statistical Theory (I)

# Lecture 9: Weak Convergence and Asymptotic Normality


LIN Zhenhua


National University of Singapore


*Adapted from Dr. Dongming Huang’s slides.


# Weak Convergence


  - Convergence in distribution is about the convergence of CDFs, not
really about random variables











LIN Zhenhua (NUS) Lecture 9 1 / 28


Convergence in distribution can be characterized by characteristic functions







**Example**

 - Let _X_ 1 _,...,Xn_ be independently and identically distributed random
variables with mean 0 and variance 1.

 - The ch.f. of _X_ 1 satisfies



_ϕX_ 1( _t_ ) = _ϕX_ 1(0) − [1]




[1] as ∣ _t_ ∣→ 0.

2 _[t]_ [2][ +] _[ o]_ [(∣] _[t]_ [∣][2][)] _[,]_




- Let _Tn_ = _X_ 1 + ⋯+ _Xn,n_ = 1 _,_ 2 _,..._ The ch.f. of _Tn_ / ~~[√]~~ _n_ is



_ϕTn_ / ~~[√]~~ _n_ ( _t_ ) = [1 − _[t]_ [2]




_[t]_ [2]

2 _n_ [+] _[ o]_ [(] _[t]_ _n_ [2]



_n_ [)]]



_n_
_,_ ∀ _t_ ∈R




- _ϕTn_ / ~~[√]~~ _n_ ( _t_ ) → _e_ [−] _[t]_ [2][/][2], the ch.f. of _N_ (0 _,_ 1) _._

- Hence _Tn_ / ~~[√]~~ _n_ → _d N_ (0 _,_ 1)


LIN Zhenhua (NUS) Lecture 9 2 / 28


If _X_ has a p.d.f. _f_ and _Xn_ has a p.d.f. _fn_, we have another way to check

whether _Xn_ →D _X_






 - Let _gn_ ( _x_ ) = [ _f_ ( _x_ ) − _fn_ ( _x_ )] _I_ { _f_ ≥ _fn_ }( _x_ ) _,n_ = 1 _,_ 2 _,..._ Then


∫ [∣] _[f]_ _n_ [(] _[x]_ [) −] _[f]_ [(] _[x]_ [)∣] _[dν]_ [=][ 2] ∫ _[g]_ _n_ [(] _[x]_ [)] _[dν]_


 - Since 0 ≤ _gn_ ( _x_ ) ≤ _f_ ( _x_ ) for all _x_ and _gn_ → 0 a.e. _ν,_ the result follows
from DCT.

 - Let _Fn_ and _F_ be the c.d.f. of _fn_ and _f_ . For any _x_ ∈ R _[k]_, let
_A_ = { _y_ ∈ R _[k]_ ∶ _yi_ ≤ _xi,i_ = 1 _,...,k_ }, then


∣∫ _n_ d _ν_ −∫ d _ν_ ∣≤∫∣ _fn_         - _f_ ∣d _ν_ → 0 _,_
_A f_ _A f_

which implies _Fn_ ( _x_ ) → _F_ ( _x_ )


LIN Zhenhua (NUS) Lecture 9 3 / 28


# Remarks on Scheff´es theorem


  - _ν_ is usually the Lebesgue measure or the counting measure

  - e.g. _Xn_ ∼ Binom( _n,pn_ ) and if _npn_ → _λ_, then _Xn_ → _D_ _X_ ∼ Poisson( _λ_ )

    - The pmf of _Xn_ is


_fn_ ( _k_ ) = ( _[n]_ _n_ [(][1][ −] _[p][n]_ [)] _[n]_ [−] _[k]_
_k_ [)] _[p][k]_


    - Note that _pn_ → 0, and _fn_ ( _k_ ) converges pointwise (for each
_k_ = 0 _,_ 1 _,_ 2 _,..._ ) to

_f_ ( _k_ ) = _e_ [−] _[λ][ λ][k]_

_k_ ! _[.]_


Hence _Xn_ →D _X_ ∼ Poisson( _λ_ ) under the counting measure.


LIN Zhenhua (NUS) Lecture 9 4 / 28


- e.g. _Xn_ ∼ _tn_, then _Xn_ →D _X_ ∼ _N_ (0 _,_ 1): The density of _Xn_ is



Γ ( _[n]_ [+][1]
_fn_ ( _x_ ) = ~~√~~ 2




_[x]_ [2]

_n_ _n_

2 [) (][1][ +]



_n_ [)]



Γ ( _[n]_ [+][1]

2 [)]
~~√~~ _nπ_ Γ ( _n_




- _[n]_ [+][1]

2



satisfies _fn_ ( _x_ ) → _ϕ_ ( _x_ ) = (2 _π_ ) [−][1][/][2] _e_ [−] _[x]_ [2][/][2] pointwise.

 - Note that we use the asymptotic property of gamma function:
Γ( _x_ + _α_ ) ∼ Γ( _x_ ) _x_ _[α]_ as _x_ →+∞, for any fixed _α_


LIN Zhenhua (NUS) Lecture 9 5 / 28


# δ -Method

If we have an approximate distribution of _θ_ [ˆ] (often by CLT), what is the
approximate distribution of _g_ ( _θ_ [ˆ] ) for a smooth function _g_ ?

  - Suppose _an_ ( _θ_ [ˆ] _n_  - _θ_ ) → _D_ _Z_, where _an_ →∞

  - When _θ_ [ˆ] _n_ ≈ _θ_, and since _g_ is differentiable, then by Taylor expansion


_g_ ( _θ_ [ˆ] _n_ ) − _g_ ( _θ_ )

≈ _g_ [′] ( _θ_ )
_θ_ ˆ _n_                - _θ_


or
_g_ ( _θ_ [ˆ] _n_ ) − _g_ ( _θ_ )

≈ _θ_ [ˆ] _n_                 - _θ_
_g_ [′] ( _θ_ )



and further



_g_ ( _θ_ [ˆ] _n_ ) − _g_ ( _θ_ ) _D_
_an_ ≈ _an_ ( _θ_ [ˆ] _n_ - _θ_ ) → _Z_

_g_ [′] ( _θ_ )



LIN Zhenhua (NUS) Lecture 9 6 / 28


# δ -method, Univariate

**Theorem.** Let _X_ 1 _,X_ 2 _,..._, _Y_ be random variables, and { _an_ } is a sequence
of positive numbers with lim _n_ →∞ _an_ = ∞ satisfying


_D_
_an_ ( _Xn_             - _c_ ) → _Y,_
where _c_ ∈R. Let _g_ be a function from R to R.


(i) If _g_ is differentiable at _c_, then


_an_ [ _g_ ( _Xn_ ) − _g_ ( _c_ )] → _D_ _g_ ′( _c_ ) _Y_
where _g_ [′] ( _x_ ) is the derivatives of _g_ at _x_
(ii) Suppose that _g_ has continuous derivatives of order _m_ - 1 in a
neighborhood of _c_, s.t.
_g_ [(] _[j]_ [)] ( _c_ ) = 0 for all 1 ≤ _j_ ≤ _m_   - 1, and _g_ [(] _[m]_ [)] ( _c_ ) ≠ 0. Then


_D_ 1
_a_ _[m]_ _n_ [[] _[g]_ [ (] _[X][n]_ [) −] _[g]_ [(] _[c]_ [)]] → _[m]_

_m_ ! _[g]_ [(] _[m]_ [)][(] _[c]_ [)] _[Y]_


LIN Zhenhua (NUS) Lecture 9 7 / 28


# Example

Suppose _X_ 1 _,...,Xn_ are i.i.d. sample from _Pλ_ with p.d.f.


_fX_ ( _x_ ) = _λe_ [−] _[λx]_ _,_ _x_ ∈[0 _,_ ∞) _,_


where the parameter _λ_ - 0 is called the rate

  - _µ_ = E _X_ = 1/ _λ_, or _λ_ = _µ_ [−][1]

  - Var( _X_ ) = _µ_ [2]

  - Let _µ_ ˆ _n_ = _X_ [¯] _n_ and _λ_ [ˆ] _n_ = _µ_ ˆ [−] _n_ [1] [=][ 1][/] _[X]_ [ ¯] _[n]_

  - CLT says that ~~[√]~~ _n_ ( _µ_ ˆ _n_  - _µ_ ) → _D_ _Z_ ∼ _N_ (0 _,µ_ 2)

  - Apply _δ_ -method with _c_ = _µ_, _g_ ( _µ_ ) = _µ_ [−][1] = _λ_

  - Since _g_ [′] ( _µ_ ) = − _µ_ [−][2] = − _λ_ [2], we have

~~√~~ _n_ ( _λ_ ˆ _n_       - _λ_ ) →− _D_ _λ_ 2 _Z_ ∼ _N_ (0 _,λ_ 2)


LIN Zhenhua (NUS) Lecture 9 8 / 28


# Examples

Suppose _X_ 1 _,...,Xn_ IID with Var( _X_ 1) = 1, _X_ _n_ = _n_ [−][1] ∑ _[n]_ _i_ =1 _[X][i]_ [,] _[c]_ [ =][ E] _[X]_ [1][,]
_an_ = ~~[√]~~ _n_, and _Z_ ∼ _N_ (0 _,_ 1)

  - If _g_ ( _x_ ) = _x_ [2],

    - if _c_ ≠ 0 then ~~[√]~~ _n_ ( _X_ ~~2~~ _n_ [−] _[c]_ [2][)] → _D_ _N_ (0 _,_ 4 _c_ 2) since _g_ ′( _c_ ) = 2 _c_ ;

    - if _c_ = 0, then _g_ [′] ( _c_ ) = 0 but _g_ [′′] ( _c_ ) = 2 ≠ 0, so we have

( ~~[√]~~ _n_ ) [2] ( _X_ ~~2~~ _n_ [−] [0][)] → _D_ _Z_ 2 ∼ _χ_ 21

  - If _g_ ( _x_ ) = _x_ [−][1] and _c_ ≠ 0, then ~~[√]~~ _n_ ( _X_ ~~−~~ _n_ 1 [−] _[c]_ [−][1][)] → _D_ _N_ (0 _,_ 1/ _c_ 4), since
_g_ [′] ( _c_ ) = − _c_ [−][2] .


LIN Zhenhua (NUS) Lecture 9 9 / 28


# Proof of (i)

Let
_Zn_ = _an_ [ _g_ ( _Xn_ ) − _g_ ( _c_ )] − _ang_ [′] ( _c_ )( _Xn_       - _c_ )


If we can show that _Zn_ = _op_ (1), then by the convergency of _an_ ( _Xn_ - _c_ )
and Slutsky’s theorem, we conclude the proof.

  - The differentiability of _g_ at _c_ implies that for any _ϵ_  - 0 _,_ there is a
_δϵ_    - 0 such that


∣ _g_ ( _x_ ) − _g_ ( _c_ ) − _g_ [′] ( _c_ )( _x_                    - _c_ )∣≤ _ϵ_ ∣ _x_                    - _c_ ∣


whenever ∣ _x_   - _c_ ∣< _δϵ_

  - On the event {∣ _Xn_  - _c_ ∣< _δϵ_ }, we have ∣ _Zn_ ∣< _ϵan_ ∣ _Xn_  - _c_ ∣

  - Consider any _η_  - 0.
If _η_ < ∣ _Zn_ ∣, then either ∣ _Xn_     - _c_ ∣≥ _δϵ_, or _η_ < _ϵan_ ∣ _Xn_     - _c_ ∣


LIN Zhenhua (NUS) Lecture 9 10 / 28


- For any _η_ - 0, _ϵ_ - 0, we have


_P_ (∣ _Zn_ ∣≥ _η_ ) ≤ _P_ (∣ _Xn_    - _c_ ∣≥ _δϵ_ ) + _P_ ( _an_ ∣ _Xn_    - _c_ ∣≥ _η_ / _ϵ_ )


- Since _an_ →∞, by Slutsky’s theorem, _Xn_ = _a_ 1 _n_ _[a][n]_ [(] _[X]_ [ −] _[c]_ [) +] _[ c]_ → _P_ _c_

- By continuous mapping, _an_ ∣ _Xn_ - _c_ ∣ →∣ _D_ _Y_ ∣

- Fixed _η_ . Choose _ϵ_ sufficiently small such that _η_ / _ϵ_ is a continuity point
of _F_ ∣ _Y_ ∣ and _P_ (∣ _Y_ ∣≥ _η_ / _ϵ_ ) is smaller than _η_

  - For a monotone function, its discontinuity points are at most countably
many

- From Eq (11), we have


limsup _P_ (∣ _Zn_ ∣≥ _η_ ) ≤ 0 + _P_ (∣ _Y_ ∣≥ _η_ / _ϵ_ ) < _η_
_n_


- Since _η_ is arbitrary, we conclude that _Zn_ = _op_ (1)


LIN Zhenhua (NUS) Lecture 9 11 / 28


# δ -method, multivariate, Theorem 1.12

Let _X_ 1 _,X_ 2 _,..._, _Y_ be random _k_ -vectors, and { _an_ } is a sequence of
positive numbers with lim _n_ →∞ _an_ = ∞ satisfying


_D_
_an_ ( _Xn_             - _c_ ) → _Y,_
where _c_ ∈R _[k]_ . Let _g_ be a function from R _[k]_ to R.


(i) If _g_ is differentiable at _c_, then


_an_ [ _g_ ( _Xn_ ) − _g_ ( _c_ )] →[∇ _D_ _g_ ( _c_ )]⊺ _Y_
where ∇ _g_ ( _x_ ) is the partial derivatives of _g_ at _x_
(ii) Suppose that _g_ has continuous partial derivatives of order _m_ - 1 in a
neighborhood of _c,_ with all the partial derivatives of order
_j,_ 1 ≤ _j_ ≤ _m_    - 1 _,_ vanishing at _c,_ but with the _m_ th-order partial
derivatives not all vanishing at _c_ . Then



_Yi_ 1⋯ _Yim._
����������� _x_ = _c_



_∂_ _[m]_ _g_
_∂xi_ 1⋯ _∂xim_



_D_ 1
_a_ _[m]_ _n_ [[] _[g]_ [ (] _[X][n]_ [) −] _[g]_ [(] _[c]_ [)]] →

_m_ !



_k_ _k_
∑ ⋯ ∑
_i_ 1=1 _im_ =1



LIN Zhenhua (NUS) Lecture 9 12 / 28


# Central Limit Theorem

Sometimes, we need to find the asymptotic distributions of a statistic to
make inference

  - e.g. asymptotic hypothesis test, confidence intervals











LIN Zhenhua (NUS) Lecture 9 13 / 28


# CLT for Triangular Arrays



















LIN Zhenhua (NUS) Lecture 9 14 / 28


# Remarks


  - Condition (1) controls the tails of _Xnj_, and is called _Lindeberg’s_
_condition_ .

  - Condition (1) is implied by either of the following

    - Lyapunov condition:



1
_σn_ [2][+] _[δ]_



_kn_
∑ E∣ _Xnj_ - E _Xnj_ ∣ [2][+] _[δ]_ → 0 for some _δ_ - 0.
_j_ =1




  - Uniform boundedness: if ∣ _Xnj_ ∣≤ _M_ for all _n_ and _j_ and
_σn_ [2] [= ∑] _j_ _[k]_ = _[n]_ 1 [Var][(] _[X][nj]_ [) →∞][.]

- In general, Condition (1) is NOT necessary for the convergence result.

- But if we assume the _Feller’s_ _condition_ :


Var( _Xnj_ )
lim = 0 _,_
_n_ →∞ [max] _j_ ≤ _kn_ _σn_ [2]


then Condition (1) is not only sufficient but also necessary


LIN Zhenhua (NUS) Lecture 9 15 / 28


# Example: Asymptotic Distribution of Empirical Variance


  - Let _X_ 1 _,...,Xn_ be i.i.d. such that E _X_ 1 [4] [< ∞][.]

  - Denote _σ_ [2] = Var( _X_ 1), _µ_ = E _X_ 1, and _m_ 2 = E _X_ 1 [2][.]

  - Let _µ_ ˆ = _X_ = _n_ [−][1] ∑ _[n]_ _i_ =1 _[X][i]_ [and] _[σ]_ [ˆ][2][ =] _[ n]_ [−][1][ ∑] _[n]_ _i_ =1 [(] _[X][i]_ [ −] _[X]_ [)][2][.]

Now we derive the asymptotic distribution of ~~[√]~~ _n_ ( _σ_ ˆ [2] - _σ_ [2] ).

  - Note that _σ_ ˆ [2] = _m_ ˆ 2 − _µ_ ˆ [2], where _m_ ˆ 2 = _n_ [−][1] ∑ _[n]_ _i_ =1 _[X]_ _i_ [2][.]

  - This motivates us to define _g_ ( _y_ 1 _,y_ 2) = _y_ 2 − _y_ 1 [2][.]

  - By multivariate CLT, for _Yn_ = ( _µ,_ ˆ _m_ ˆ 2) [⊺], we have
~~√~~ _n_ ( _Yn_  - _c_ ) → _D_ _N_ (0 _,_ Σ), where _c_ = ( _µ,m_ 2) and Σ = Cov([ _X_ 1 _,X_ 12 []][⊺][)][.]

  - Observe that ∇ _g_ ( _y_ 1 _,y_ 2) = (−2 _y_ 1 _,_ 1) [⊺] ≠ 0.

  - By _δ_ -method,

~~√~~ _n_ ( _σ_ ˆ2 − _σ_ 2) → _D_ _N_ (0 _,_ (−2 _µ,_ 1)Σ(−2 _µ,_ 1)⊺) _._


LIN Zhenhua (NUS) Lecture 9 16 / 28


# Needs for the Asymptotic Approach


  - In many applications of statistics, the distribution of a given statistic
_Tn_ ( _X_ ) is needed, but the exact distributions of _Tn_ ( _X_ ) is not
available or too complicated to deal with

  - The limiting distribution is used as an approximation to the
distribution of _Tn_ ( _X_ ) in the situation with a large but actually finite
_n_


    - by using CLT, SLLN, WLLN, _δ_ -method, etc.

    - We treat a sample _X_ = ( _X_ 1 _,...,Xn_ ) as a member of a sequence of
samples corresponding to _n_ = 1 _,_ 2 _,..._

    - Similarly, a statistic _T_ ( _X_ ), often denoted by _Tn_ to emphasize its
dependence on the sample size _n_, is viewed as a member of a sequence
_T_ 1 _,T_ 2 _,..._

  - In addition, the asymptotic approach requires less stringent
mathematical assumptions than does the exact approach


LIN Zhenhua (NUS) Lecture 9 17 / 28


# Asymptotic Unbiasedness













LIN Zhenhua (NUS) Lecture 9 18 / 28


# Remarks


  - Like the consistency, the asymptotic bias is a concept relating to
sequences { _Tn_ } and { [˜] _bTn_ ( _P_ )}

  - When both the exact bias _bTn_ ( _P_ ) and the asymptotic bias [˜] _bTn_ ( _P_ )
exist, they are NOT necessarily the same

  - If _Tn_ is a consistent estimator of _θ_, then _Tn_ = _θ_ + _op_ (1), and thus _Tn_
is asymptotically unbiased

    - _g_ ( _Tn_ ) is asymptotically unbiased for _g_ ( _θ_ ) for any continuous function _g_
_a.s._

    - In the example of estimating 1/ _µ_ by _Tn_ = 1/ _X_ [¯], _Tn_ → 1/ _µ_ by the
SLLN and the continuous mapping. Hence _Tn_ is asymptotically
unbiased, although _ETn_ may not be well-defined.


LIN Zhenhua (NUS) Lecture 9 19 / 28


# Asymptotic Mean Squared Error (amse)

Like the bias, the variance and MSE of an estimator is not well defined if
its second moment does not exist









LIN Zhenhua (NUS) Lecture 9 20 / 28


# Remarks


  - It holds that “amse= asym. bias [2] + asym. variance” if they are all
well defined

  - In the definition, the amse and asymptotic variance are the same if
and only if _EY_ = 0

  - In the definition, one can show that


_EY_ [2] ≤ liminf _n_ →∞ _[E]_ [ [] _[a]_ _n_ [2] [(] _[T][n]_ [−] _[ϑ]_ [)][2][]]


    - Proof is left for exercise: use Skorohod’s theorem and Fatou’s lemma

    - The equality holds if and only if { _a_ [2] _n_ [(] _[T][n]_ [−] _[ϑ]_ [)][2][}] [is] [uniformly] [integrable.]

    - In other words, the amse is no greater than the exact mse and they are
equal under a certain condition.


LIN Zhenhua (NUS) Lecture 9 21 / 28


# Asymptotic Relative Efficiency

Let _Tn_ and _Tn_ [′] [be] [two] [estimators] [of] _[ϑ]_

  - The **asymptotic** **relative** **efficiency** **of** _Tn_ [′] **[w.r.t.]** _[T][n]_ [is] [defined] [to] [be]


_eTn_ ′ _,Tn_ ( _P_ ) = amse _Tn_ ( _P_ )/ amse _Tn_ ′ ( _P_ )


  - _Tn_ is said to be **asymptotically** **more** **efficient** **than** _Tn_ [′] [if] [and] [only] [if]


limsup _eTn_ ′ _,Tn_ ( _P_ ) ≤ 1
_n_


for any _P_ and < 1 for some _P_

  - Historically, the “efficiency” of an estimator _T_ of _θ_ refers to
1/[ _I_ ( _θ_ )MSE _T_ ( _θ_ )], where _I_ ( _θ_ ) is the Fisher information of _θ_ .
So the definition above should be understood as

_eTn_ ′ _,Tn_ ( _P_ ) = [asy.] asy. [ef] eff. [.] [of] of _[T]_ _T_ [ ′] _nn_


LIN Zhenhua (NUS) Lecture 9 22 / 28


# A corollary of δ -method









See Theorem 2.6 in the textbook for the multivariate version.


LIN Zhenhua (NUS) Lecture 9 23 / 28


# Example





Let _T_ 1 _n_ = _n_ [1] [∑] _j_ _[n]_ =1 _[I]_ { _Xj_ =0}

  - _T_ 1 _n_ is unbiased and has mse _T_ 1 _n_ ( _θ_ ) = _e_ [−] _[θ]_ (1 − _e_ [−] _[θ]_ )/ _n_

  - By CLT, ~~√~~ _n_ ( _T_ 1 _n_  - _τ_ ) →D _N_ (0 _,e_  - _θ_ (1 − _e_  - _θ_ ))

  - So amse _T_ 1 _n_ ( _θ_ ) = mse _T_ 1 _n_ ( _θ_ )


LIN Zhenhua (NUS) Lecture 9 24 / 28


# Example (Cont.)





Next, consider _T_ 2 _n_ = _e_ [−] _X_ [¯]

  - By CLT, ~~[√]~~ _n_ ( _X_ [¯]  - _θ_ ) →D _N_ (0 _,θ_ )

  - By _δ_ -method, we have ~~[√]~~ _n_ ( _T_ 2 _n_  - _τ_ ) →D _N_ (0 _,e_ −2 _θθ_ )

  - So _T_ 2 _n_ is asymptotic unbiased and amse _T_ 2 _n_ ( _θ_ ) = _e_ [−][2] _[θ]_ _θ_ / _n_

  - Note that _ET_ 2 _n_ = _e_ _[nθ]_ [(] _[e]_ [−][1][/] _[n]_ [−][1][)] and _nbT_ 2 _n_ ( _θ_ ) → _θe_ [−] _[θ]_ /2. The exact bias
of _T_ 2 _n_ is not _o_ (1/ _n_ )


LIN Zhenhua (NUS) Lecture 9 25 / 28


# Example (Cont.)

The asymptotic relative efficiency of _T_ 1 _n_ w.r.t. _T_ 2 _n_ is


_eT_ 1 _n,T_ 2 _n_ ( _θ_ ) = _θ_ /( _e_ _[θ]_         - 1) < 1 _,_ ∀ _θ_         - 0


This shows that _T_ 2 _n_ is asymptotically more efficient than _T_ 1 _n_


LIN Zhenhua (NUS) Lecture 9 26 / 28


# Asymptotic Confidence Intervals

Let _θ_ [ˆ] _n_ be an estimator of a scalar parameter _θ_ 0 based on a sample of size
_n_ . If
~~√~~ _n_ ( _θ_ ˆ _n_       - _θ_ 0) �→D _N_ (0 _,V_ ) _,_


then for large _n_,
_θ_ ˆ _n_ ≈ _D_ _N_ ( _θ_ 0 _,_ _[V]_

_n_ [)] _[.]_













LIN Zhenhua (NUS) Lecture 9 27 / 28


# Example: MLE for the Exponential Mean

Let _X_ 1 _,...,Xn_ be i.i.d. drawn from the density _f_ ( _x_ ; _λ_ ) = _λ_ [−][1] _e_ [−] _[x]_ [/] _[λ]_ for
_x_ - 0 and _λ_ - 0

  - Note that _λ_ = E( _X_ 1) is the population mean and Var( _X_ 1) = _λ_ [2]

  - Estimate _λ_ by the sample mean



_λ_ ˆ = _X_ ¯ = [1]

_n_



_n_
∑ _Xi_
_i_ =1




- By CLT,
~~√~~
_n_



�→D _N_ (0 _,_ 1) _._
_λ_ [(] _[λ]_ [ˆ][ −] _[λ]_ [)]




- By Slutsky’s theorem,
~~√~~
_n_



( _λ_ [ˆ]  - _λ_ ) �→D _N_ (0 _,_ 1) _._
_λ_ ˆ




- Asymptotic (1 − _α_ ) confidence interval for _λ_ is

_X_ ¯ ± _z_ 1− _α_ /2 ~~√~~ _X_ ¯ _n_
_n_

LINhZhenhua _X_ ¯(NUS) l _θ_ b th Lecturel i9 i i l 28 / 28


