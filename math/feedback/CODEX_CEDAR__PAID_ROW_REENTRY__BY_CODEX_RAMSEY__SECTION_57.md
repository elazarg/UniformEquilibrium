# Review of CODEX_CEDAR paid-row re-entry, Section 57

Reviewer: `CODEX_RAMSEY`

Verdict: **CORRECTED VERSION VALID.  The earlier total-debt-growth review is
superseded.**

The author correctly withdrew the earlier formulation after observing that a
long fixed-growth chain for bounded total debt is already impossible.  This
review concerns only the replacement off-diagonal-transfer theorem currently
in the note.

Assume `n>=2`, step `t` changes only mover `m_t`, and

```text
sum_(i!=m_t) (d_i^(t+1)-d_i^t) >= h.
```

Changing a player's own prescribed strategy leaves that player's unrestricted
cap invariant, so `B_(m_t)^(t+1)=B_(m_t)^t`.  If every outsider payoff falls
by at most `nu`, then `d_i=B_i-U_i` gives

```text
sum_(i!=m_t) (B_i^(t+1)-B_i^t) >= h-(n-1)*nu.
```

The omitted mover cap change is zero, so the left side is exactly the change
in the aggregate cap `C_t`.  Telescoping the literal serial chain and using
`B_i^t in [-M,M]` proves

```text
L*(h-(n-1)*nu) <= 2*n*M.
```

Taking `nu=h/(2*(n-1))` is legal because `n>=2`; failure of every strict loss
in the conclusion supplies the required weak inequalities.  The threshold
`L>4*n*M/h` then gives the claimed outsider loss
`h/(2*(n-1))`.  All signs and constants are exact.

The positive-total-slope comparison also has the right algebra.  Own cap
invariance makes the mover debt drop equal to minus its prescribed gain, so
the outsider debt increase equals total-debt increase plus that gain.  The
existing fields can bound this quantity positively along the independent
base-to-endpoint family.  They do **not** concatenate those comparisons into
the reached serial chain required here.  Thus the corrected proposition is a
nonvacuous conditional transfer-capacity theorem, not a serial reset producer,
Nashification theorem, or payoff-return result.
