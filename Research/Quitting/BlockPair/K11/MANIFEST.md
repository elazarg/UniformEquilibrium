# Period-eleven BlockPair research surface

The maintained entry point is `Research.Quitting.BlockPair.K11`. It groups
the parameterized interval-certificate interface, the row-zero adapter, the
conditional Krawczyk consumer, and the compositional conditional compiler.
Active-equation semantics are owned by
`UniformEquilibrium.Quitting.Examples.BlockPair.K11ActiveEquationInterval`.

The umbrella dependency closure is the authoritative module inventory.
Concrete numeric payloads and their instance assembly are owned by
`Experiments/certsearch/block_pair/K11`. Generated certificates, audit probes,
and modules requiring `native_decide` are outside the maintained Research
boundary. Admitting another module requires a proof review, a trust check, and
an explicit umbrella import.

The 29 maintained implementation modules are:

```text
ClearedSemantic                     ConditionalAbsorption
ConditionalBlock                    ConditionalBlockData
ConditionalData                     ConditionalExactNash
ConditionalNash                     ConditionalPackage
ConditionalProfile                  ConditionalUniformPayoff
ContinueMassPhase                   ContinueMassRoot
EndpointSemantic                    EndpointSemanticOne
EndpointSemanticThree               EndpointSemanticTwo
EndpointSemanticZero                EvalImmediateReward
FourPlayerExpectation               ImmediateSemantic
ImmediateSemanticOne                ImmediateSemanticThree
ImmediateSemanticTwo                ImmediateSemanticZero
KrawczykConditionalConsumer         KrawczykConditionalData
KrawczykConditionalSemantic         PhaseValueRecurrence
RowZeroSemantic
```

`ConditionalPackage` is the sole conditional strategic compiler in the
maintained surface. Active-equation semantics use the production declaration
named above. `PhaseValueRecurrence` connects directly to the canonical
recurrence in `K11System`; the maintained surface therefore contains no
separate scalar-numerator consumer. `K11KrawczykData` is the sole numeric-data
interface consumed by the Krawczyk semantic and existence theorems. The finite
arithmetic certificate contains only interval/rational checks; the checker
takes preconditioner injectivity directly and returns the unique canonical zero
in the certified ball, together with its interval-box membership.
