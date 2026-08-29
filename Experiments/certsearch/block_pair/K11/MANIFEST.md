# K11 certificate evidence

The maintained local entry point is `Experiments.certsearch.block_pair.K11`.
It contains concrete numeric evidence for one period-eleven Krawczyk
certificate, the conditional Krawczyk checker interface, and their assembly
into a checked `K11KrawczykData` instance. Research does not import this lane.

The eight implementation modules are:

```text
DyadicData                         JacobianCache
KrawczykConditionalConsumer        KrawczykConditionalData
KrawczykConditionalSemantic        KrawczykInstance
Preconditioner                     RowZeroCacheData
```

`DyadicData`, `Preconditioner`, `JacobianCache`, and `RowZeroCacheData` are
concrete checked-in payloads. `KrawczykConditionalData` defines
`K11KrawczykData` and its interval-arithmetic caches; `KrawczykConditionalSemantic`
links those caches to the real-valued Krawczyk step; `KrawczykConditionalConsumer`
proves the conditional existence-and-uniqueness theorem consumed by an
instance. `KrawczykInstance` is the sole assembly point. The JSON integrity
record and `scripts/check_k11_generated_data.py` check all four payloads at
the source and logical levels; they do not regenerate the numeric computation.

## Provenance and limitations

The surviving `Preconditioner.lean` header names
`q117_krawczyk_certificate.json` and
`q117_emit_lean_preconditioner.py`. Neither artifact was present in this
repository or the audited predecessor checkout. The `RowZeroCacheData.lean`
header likewise names `q117_verify.py`, which was not present. `DyadicData.lean`
and `JacobianCache.lean` have no surviving source-data or producer record. The
complete `GameTheory` source tree at revision
`171e014480bfd59f09403abc68af45b7f2c44fb5` was also searched and contains none
of the named q117 artifacts or a matching K11 JSON, Python, dyadic-data,
Jacobian-cache, row-zero-cache, or preconditioner path.

The four checked-in Lean payload files are therefore classified as migrated
evidence without a reproducible original producer. The structured JSON record
stores full-file hashes and formatting-independent logical hashes of the exact
dyadic box, preconditioner, Jacobian, and row-zero cache payloads.
`scripts/check_k11_generated_data.py` deterministically checks those hashes,
the payload shapes, dyadic precisions and scale, interval ordering, matrix row
routing and final constructors, and the row-zero absolute-sum cache. It is a
freshness and integrity check only: it neither reconstructs the missing JSON
nor recomputes any payload from the game data. Thus the record does not supply
independent numerical provenance, an adapter from recovered source data, or
any stronger mathematical claim than the existing conditional Lean consumers.
