# Finite-state homogeneous Markov martingale variation

Let \(\Omega\) be a finite nonempty set, \(K(x,y)\) a time-homogeneous
stochastic transition matrix on \(\Omega\), and \(X_0=x_0\),
\(X_{t+1}\mid X_t\sim K(X_t,\cdot)\). Fix a finite horizon \(H\).
For each \(0\le t\le H\), let \(v_t:\Omega\to[0,1]\) satisfy the
backward harmonic equations

\[
v_t(x)=\sum_{y\in\Omega}K(x,y)v_{t+1}(y)
\qquad (t<H,\ x\in\Omega).
\]

Is the following bound valid for every such choice of data?

\[
\mathbb E_{x_0}\!\left[
  \sum_{t=0}^{H-1}|v_{t+1}(X_{t+1})-v_t(X_t)|
\right]\le |\Omega|.
\]

Prove it or give a finite counterexample. The constant must be independent
of the horizon and of the entries of \(K\). Replacing the total variation
by a separate bound of one for the contribution attributed to each current
state is not valid; a proof of the displayed aggregate inequality cannot
rely on that stronger per-state assertion.

The bound would supply the finite-horizon input for a Markov-variation
lemma used in a quitting-game structure argument. The question concerns
only the finite homogeneous Markov chain and the displayed harmonic data;
it assumes no game-theoretic strategy or equilibrium.
