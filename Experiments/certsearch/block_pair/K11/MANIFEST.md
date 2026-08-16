# K11 certificate evidence

The maintained local entry point is `Experiments.certsearch.block_pair.K11`.
It contains concrete numeric evidence for one period-eleven Krawczyk
certificate and its assembly into the reusable `K11KrawczykData` Research interface.
Research does not import this lane.

The five implementation modules are:

```text
DyadicData                         JacobianCache
KrawczykInstance                   Preconditioner
RowZeroCacheData
```

`DyadicData`, `Preconditioner`, `JacobianCache`, and `RowZeroCacheData` are
concrete checked-in payloads. `KrawczykInstance` is the sole assembly point.
The JSON integrity record and `scripts/check_k11_generated_data.py` check all
four payloads at the source and logical levels; they do not regenerate the
numeric computation. Historical provenance is recorded only in `TRANSITION.md`.
