# Period-eleven BlockPair research surface

The maintained entry point is `Research.Quitting.BlockPair.K11`. It groups
exact rational and interval payload interfaces, the row-zero adapter, the
conditional Krawczyk consumer, and the compositional conditional compiler.
Active-equation semantics are owned by
`UniformEquilibrium.Quitting.Examples.BlockPair.K11ActiveEquationInterval`.

The umbrella dependency closure is the authoritative module inventory.
Generated certificates, audit probes, and modules requiring `native_decide`
are outside the maintained trust boundary. Admitting another module requires a
proof review, a trust check, and an explicit umbrella import.

The 32 maintained implementation modules are:

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
JacobianCache                       KrawczykConditionalConsumer
KrawczykConditionalData             KrawczykConditionalSemantic
PhaseValueRecurrence                Preconditioner
RowZeroCacheData                    RowZeroSemantic
```

`ConditionalPackage` is the sole conditional strategic compiler. The obsolete
parallel `ConditionalStrategicCompiler` body is not part of the maintained
surface. The former Research active-equation adapter was also removed because
its theorem is identical to the production declaration named above. The
consumerless scalar numerator chain was removed after `PhaseValueRecurrence`
was connected directly to the canonical recurrence in `K11System`.
