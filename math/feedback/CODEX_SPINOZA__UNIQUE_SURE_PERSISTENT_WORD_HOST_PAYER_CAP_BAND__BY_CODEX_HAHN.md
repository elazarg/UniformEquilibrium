# Review of the unique-sure persistent-word host-payer cap band

Reviewer: CODEX_HAHN

Reviewed note:
`notes/CODEX_SPINOZA__UNIQUE_SURE_PERSISTENT_WORD_HOST_PAYER_CAP_BAND.md`
at exact SHA256
`a483dcd138c54ca99aa6041effc78345593015853ec35ef1f6d41c4bedc63538`.

## Verdict

**PASS as exact ordinary mathematics and as a branch-local source
adapter.**  The host/payer identification, cap-band constants, cut location,
and deleted-survival statement are correct under the note's stated diagonal
word hypotheses.  The note also states the correct boundary: the target is a
paid sibling with retained deleted-player reach, not an exact-root
descendant or a renewable source.

## Claim checked

For a literal exact payoff-root word whose innermost roots converge to a
product root with one sure quitter \(k\), and whose outer diagonal has the
stated positive survival products, the note claims:

1. \(k\) is the unique positive deleted-survival host;
2. every outsider debt and cap-anchored ledger coordinate tends to zero;
3. \(k\)'s debt and ledger remain uniformly positive; and
4. a cap-band update of \(k\) gives a fixed payoff gain, a uniformly reached
   cut strictly inside the word, and exact preservation of the
   \(k\)-deleted clock through the inner boundary.

## Detailed audit

### Deleted-survival geometry

Deleting \(k\) removes the factor
\(1-q_{n,0,k}\to0\).  The remaining inner factor converges to

\[
\prod_{i\ne k}(1-q_i)>0,
\]

and the assumed outer deleted-survival product has a positive limit.  Thus
\(\beta_{n,k}\) has a positive eventual floor.  Joint survival retains the
near-zero \(k\)-factor, as does every \(i\)-deleted survival for
\(i\ne k\).  Hence the other limits in equation (5) are correct.

The assumption about the outer diagonal is doing real work here.  Mere
absence of a sure outer row would not by itself supply a uniform product
floor; the stated summability and positive limiting diagonal products do.

### Debt concentration and payer identification

Iterating the checked exact-payoff-root inequality gives

\[
d_i(W_n\triangleright X_n)\le
\beta_{n,i}d_i(X_n).
\]

The complete tail debts are uniformly bounded, so every outsider debt tends
to zero.  Since the full profile is actual and has total debt at least
\(D_*\), the owner debt is eventually at least \(D_*/2\).

The cap-anchored playerwise identity

\[
d_i(\Sigma_n)=\Lambda_{n,i}+\alpha_n d_i(X_n)
\]

has two nonnegative terms.  It therefore forces every outsider ledger
coordinate to zero.  For \(k\), \(\alpha_n\to0\) and bounded tail debt leave
\(\Lambda_{n,k}\ge D_*/3\) eventually.  Thus host and payer really are the
same fixed player; no aggregate-pigeonhole ambiguity remains.

### Cap-band estimates

Apply the checked cap-band construction at width \(e=D_*/4\).  The owner
debt floor \(d_k(\Sigma_n)\ge D_*/2\) gives

\[
U_k(\widehat\Sigma_n)-U_k(\Sigma_n)
 \ge d_k(\Sigma_n)-e\ge D_*/4
\]

and target owner debt at most \(D_*/4\).  Both the bad-mass and common-prefix
reach inequalities then give

\[
\operatorname{badMass}_n\ge {D_*\over8R},
\qquad
\Pr(\text{joint survival through }c_n)\ge {D_*\over8R}.
\]

The constants and inequality directions are correct.  Positivity of \(R\)
is explicit.

### Cut location

With the repository's cutoff convention, survival through the word of
length \(m_n\) is the cutoff-\(m_n\) survival \(\alpha_n\).  If
\(c_n\ge m_n\), monotonicity would bound the displayed cut reach above by
\(\alpha_n\to0\), contradicting its fixed floor.  Hence
\(c_n<m_n\).  Because the innermost row is the final row of the word, the
endpoint \(c_n=m_n-1\) remains possible, exactly as the note says.

### What the target preserves

The cap-band update changes only player \(k\).  Therefore every
\(k\)-deleted stopping calculation is literally unchanged at every horizon,
including the boundary \(m_n\).  Conversely, this gives no lower bound on
ordinary joint reach after the update: the changed player can receive Quit
mass before the inner boundary.  Equality of live root actions strictly
before \(c_n\) also does not preserve their Nash property against the new
continuation.  The nonclaims accurately mark both failures.

## Boundary tests

- If the outer deleted-survival product for \(k\) is allowed to vanish, the
  host floor can fail even though each finite outer row is nonsure.  This is
  excluded by the input.
- If the payer differs from the host, changing the payer can kill the only
  live deleted clock.  The predecessor note's explicit regression witnesses
  this, and the current unique-sure debt concentration is exactly what rules
  that case out.
- Positive \(k\)-deleted reach is compatible with zero target joint reach:
  a target law that moves its bad mass to a finite receiver before \(m_n\)
  supplies the elementary counterexample.  Thus equation (15) cannot be
  promoted to a chronological reach statement.

## Exact surviving contribution

The result removes the nonhost-payer branch on the literal persistent word
and locates a fixed-gain actual host update at a uniformly reached cut inside
that same word.  It does not consume the branch.  The remaining datum is the
location of the cap-band receiver: a receiver at or beyond the inner
boundary carries redirected bad mass through that boundary, whereas an
earlier receiver leaves only a paid preboundary sibling whose changed
continuation need not satisfy the old root equations.

