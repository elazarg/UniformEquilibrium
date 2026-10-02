# Persistent two-label amplification from finite packet words

Author: `CHATGPT_EXTERNAL`
Status: `PROOF_DRAFT`

## Exact question

Does arbitrarily late availability of finite product-root words with strictly
positive absorption after every one-player deletion suffice to construct one
literal executable chronology with two fixed nonsummable marginal Quit
streams, without transporting any frozen semantic source?

This addresses only the survival field. Prescribed-payoff discrepancy, debt
forcing, and small initial debt remain separate.

## Why it could matter

The two-label clock characterization reduces all joint and one-player-deleted
suffix survival limits to two distinct nonsummable marginal Quit streams. If
finite frozen packet roots can be concatenated and repeated literally, clock
reprojection has zero error even though their reached semantic sources change.

## Sources checked

- [`../questions/PERSISTENT_TWO_LABEL_HAZARDS.md`](../questions/PERSISTENT_TWO_LABEL_HAZARDS.md).
- The submitted proof invokes the frozen radial packet theorem as a source of
  the finite words. Exact compatibility of that invocation remains to be
  audited against the conference's existing packet results.

## Work

### Theorem proposed

Let `I` be finite. Suppose that at arbitrarily late ranks `n` there is a
finite nonempty word of product roots

```text
W_n=(x_(n,0),...,x_(n,L_n-1))
```

such that, for every player `i`,

```text
S_(-i)(W_n)
 = product_(s<L_n) product_(j!=i) (1-q_(n,s,j)) < 1,
q_(n,s,j)=P_(x_(n,s,j))(Quit).
```

Then there exist distinct fixed labels `a,b`, a subsequence of words, finite
repetition counts, and one literal concatenated root sequence `xhat_t`, every
root of which is a selected packet root, such that the marginal hazard sums of
`a` and `b` diverge from every suffix. Actual and nominal hazards agree
pointwise, so the summable reprojection error is zero and fixed-fraction
retention holds with `theta=1`.

### 1. Two positive labels in each packet

For a word `W`, put

```text
H_W(j)=sum_(s<|W|) q_(s,j),
A(W)={j : H_W(j)>0}.
```

If `A(W)` is empty, every deleted survival is one. If `A(W)={c}`, then after
deleting `c` all remaining players Continue surely and `S_(-c)(W)=1`.
Therefore the hypothesis implies `|A(W)|>=2`.

Choose two labels in every word. Finitely many unordered label pairs exist,
so an infinite subsequence has one fixed pair `{a,b}`. On every selected word,

```text
H_k(a)>0,  H_k(b)>0.
```

Any other eventual finite-rank condition, including a prescribed vanishing
mesh scale, may be retained while passing to this subsequence.

### 2. Finite repetition

Put `h_k=min(H_k(a),H_k(b))>0` and choose an integer
`R_k>=1/h_k`. Let `V_k` consist of `R_k` consecutive copies of `W_k`. Then
each of `a,b` contributes at least one unit of marginal hazard in `V_k`.
Concatenating `V_0,V_1,...` makes both marginal series divergent. Removing a
finite prefix preserves divergence.

### 3. Literal source matching for clocks

Let `sigmahat` be the behavioral profile defined by the concatenated roots,
and `sigmahat^t` its reached residual profile after `t` all-Continue outcomes.
Its literal semantic pair `z_t` satisfies

```text
z_t=Phi_(xhat_t)(z_(t+1)).
```

Every selected word is used unchanged as a finite prefix of its actual future
continuation. Changing that continuation changes the predecessor semantic
pair but does not change any product root within the word. Consequently every
marginal hazard and every joint or deleted survival product internal to a word
is identical to its nominal value.

### 4. Clock conclusion

For every deleted player `i`, at least one of `a,b` remains. Its divergent
marginal hazard forces the corresponding deleted survival to zero from every
suffix; joint survival follows. Thus the two-label consumer applies with
zero hazard error or `theta=1`.

## Checks and open objections

- Audit whether the cited frozen radial packet theorem really provides a
  finite word satisfying every strict deleted-survival inequality at
  arbitrarily late ranks.
- Audit whether finite repetition is legitimate for the isolated clock claim
  even though it generally destroys frozen semantic/reset properties.
- Compare against Cedar's already-reviewed block selection, label freezing,
  and literal root concatenation to determine novelty.
- No claim is made that reached semantic states equal frozen tangent sources,
  or that atom orientation, prescribed values, debt forcing, or small initial
  debt survive the splice.

## Feedback wanted

1. Is the theorem valid exactly as a survival-only statement?
2. Does the existing frozen packet result satisfy its hypothesis?
3. Does this remove any live producer obligation, or only restate the known
   separation between clock preservation and semantic/debt control?
