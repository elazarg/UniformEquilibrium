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
Historical provenance is recorded only in `TRANSITION.md`.
