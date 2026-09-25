# Lean proof sources

These handwritten Lean modules import the freshly generated `Leanisa` model.
The [full validation campaign](../docs/validation.md) builds them as one
library and audits the transitive axioms of every declaration owned by the
project. The theorem statements define the exact hypotheses; the summary
below is a guide to the source.

| Area | Representative modules | Established scope |
| --- | --- | --- |
| Memory and execution policies | `Memory`, `Lookup`, `Instructions`, `Runner`, `Arithmetic`, `Observations`, `Control`, `Dereference`, `Compression`, `WholeISA` | Observation preservation, finite-index lookup, conditional six-instruction simulation, and bounded scanning-runner results with exact state, fuel, sentinel, and failure boundaries. Completion, address equations, and deferred Cell equalities remain explicit where required. |
| Canonical encoding | `Encoding`, `EncodingChecks` | Encode/decode round-trip, accepted-row equality, injectivity, and malformed-row rejection for typed Sail instructions. |
| Base arithmetic and addresses | `FieldLoops`, `PowerLoops`, `QuotientRepresentation`, `PolynomialMultiplication`, `PolynomialExponentiation`, `GeneratorOrder`, `RootOrderExact`, `BaseField` | Actual extracted `advance`, `kmul`, and `gpow` interpretation; quotient-ring multiplication, exact root order, and unconditional base-field structure. |
| Extension arithmetic and inverse | `ExtensionRepresentation`, `ExtensionMultiplication`, `ExtensionField`, `ExtensionInverse`, `BaseItoh`, `F1e5b`, `F1e5c` | Actual `emul` interpretation, cubic field structure, and a source-shaped 192-bit inverse equal to `inverseRef` on all words. |
| Supported address policies | `SupportedAddressDomain`, `SupportedWholeISA`, `EncodedOperands`, `EncodedArithmeticControl`, `EncodedDereference`, `EncodedBlake` | Supported finite domains and effective-address equations for represented encoded offsets; conditional policy witnesses including aliases and ordered BLAKE accesses. |
| Indexed execution | `CircularProbe`, `BuilderSupported`, `IndexedScans`, `IndexedCorrectness`, `IndexedRunner` | Exact built-index lookup and full indexed/scanning runner-result equality under source size premises. |

`Checks/` modules and the `*Checks.lean` modules exercise boundary cases and
logical false controls. They are built with the library but are not substitutes
for the general theorem statements.

The proof policy permits only `propext`, `Classical.choice`, and `Quot.sound`
in owned declarations' transitive axiom sets. A passing axiom audit is a
separate gate from compilation. The accepted results do not prove that actual
Rust execution refines Sail, that Sail's compiler is correct, or that O1/O2a/O2b
generated results satisfy the whole-ISA policy for all inputs. See the
[correspondence boundary](../docs/correspondence.md) and
[release scope](../docs/release.md).
