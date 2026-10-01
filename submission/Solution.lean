import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless signature with a narrow overlapping-window gate and PORS prefixes

S=6032 signature bytes, W=16128 witness bytes, K=131072 cache bytes.
The declared C=10492 combines accepting bound10429 and witness charge63.
The five WOTS targets are all185. For oracle words A,B,C,D, the selector
uses BC when B's top bit is clear and A's top bit is set, otherwise AB;
when B's top bit is set, it uses CD exactly when A's high nine bits are
at least125, otherwise retaining the invalid AB pair. Every padding-clear
output has1923*2^118 preimages; the global fiber bound is the same.

The signing envelope is bounded by
2^(115258/131072)*1.0278029*1.0112990247^5 <=2.
The joint security bounds use coefficient197691/100000 and split1027*2^102.
The actual2^-700 large-budget tail implies the intermediate2^-48 bound.
Sign and expand share the literal selector:17 instructions and23 cycles
including its caller jump. The64-cycle per-trial termination bound holds.

PR174's descriptor bits5..7 encode the PORS heap path modulo8. The verifier
checks that prefix and specializes up to two nonfinal authentication folds.
The312 public prefix blocks, scheduler/security transport, protected root,
and aggregate22-cycle credit are retained. The root takes11 instructions
following the public movement of constant6 initialization into digest setup.
The narrow selector adds at most one instruction per layer; uniform185
removes nine chain cycles and one top-layer target correction in total.

The exported certificate covers the four images, termination, completeness,
honest compression budgets,127-bit security and accepting verifier cost.
These are proof obligations; no measured instruction/HASH profile is claimed.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 16128 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2304 } := rfl

theorem certificate : SigGolf.Certificate submission 10492 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
