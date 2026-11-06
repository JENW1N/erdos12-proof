# Verification report — JSP-000051 / Erdős Problem 12

**Overall verdict: Verification passed.** The source at
[`f959d3865c3a604cfdc2a925a29a1b66f2ad6477`](https://github.com/JENW1N/erdos12-proof/tree/f959d3865c3a604cfdc2a925a29a1b66f2ad6477)
formally answers all three numbered questions of Erdős Problem 12, with the
answers yes, no, and yes. The submitted source, a separate literal statement,
the positive-integer convention, transitive axioms, kernel replay, and an
external Nanoda check passed as specified below. This is a pre-submission
agent-assisted self-check, not independent human peer review or organizer approval.

| Required question | Judgment | Evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | Yes | Literal three-question statement comparison; definitions, quantifiers, and boundaries reviewed below. |
| Did the specified source commit pass the executed verification? | Yes | Fresh compilation, all target checks, kernel replay, and external comparison returned exit code 0. |
| Does it fully solve the specified original problem? | Yes, for the three numbered questions | The three answers are combined in `Erdos12AllParts.all_parts`; all original hypotheses and quantifiers are retained. |
| Does it meet the Lean completeness requirements of this review? | Meets | No placeholder or extra-axiom dependency; all three statements and the two claimed strengthenings are covered. |

## Pinned evidence and scope

- Verification completed: 2026-11-06T05:05:46.681079+00:00.
- Source repository: `https://github.com/JENW1N/erdos12-proof`, branch `main`,
  checked commit `f959d3865c3a604cfdc2a925a29a1b66f2ad6477`. The public branch and downloaded source/PDF hashes
  matched the local artifacts; see [publication.json](publication.json).
- The source tree was unchanged after checking. The later evidence commit
  only publishes records about this selected source version.
- Awards catalog base reviewed: `f8801a856529dce27e738c6b305e46d76e7c387c`,
  `problems/catalog-0001-0100.md`, JSP-000051. There was no submission PR yet
  when this pre-submission check was performed.
- Original source: [Erdős Problem 12](https://www.erdosproblems.com/12).
  Direct retrieval was blocked. The full formal statement and its prose were
  checked at [Formal Conjectures commit 7d1a8c9912747679d0093f6d1216420c33ee5ffa](https://github.com/google-deepmind/formal-conjectures/blob/7d1a8c9912747679d0093f6d1216420c33ee5ffa/FormalConjectures/ErdosProblems/12.lean),
  and the original Property P and open questions were reviewed in
  [Erdős–Sárközy (1970), pp. 97–98](https://users.renyi.hu/~p_erdos/1970-13.pdf).
- The scope is the three numbered questions, together with the explicitly
  claimed uniform reciprocal bound and parameterwise-density strengthening.
  Known auxiliary variants listed in Formal Conjectures are historical context,
  not additional claimed new results.

## Mathematical correspondence and coverage

A good set is infinite and has no three distinct elements a,b,c with a<b,
a<c, and a dividing b+c. Requiring divisibility and the two strict inequalities
to imply b=c is equivalent. The two larger summands may coincide; this is not
the stronger prohibition of repeated summands. Each counting function uses
`A ∩ Icc 1 N`, not a finite example or a restricted family of sets.

| Original requirement | Pinned formal target | Correspondence and coverage |
| --- | --- | --- |
| Some infinite good set has positive liminf of its count divided by square root N. | `Erdos12AllParts.part_i` | Full existential statement, real liminf, all natural cutoffs. The prior construction proves a positive finite lower limit, so real-valued liminf is used correctly. |
| Is there one c>0 such that every infinite good set has infinitely many strict power-saving cutoffs? | `Erdos12AllParts.part_ii` | Full negative answer, with the existential c outside the universal A. It refutes the original assertion, not merely one exponent or one cutoff. |
| Does every infinite good set have a convergent reciprocal series? | `Erdos12AllParts.part_iii` | Full universal quantifier over good sets and summability of the complete subtype-indexed reciprocal series. |
| All three answers together. | `Erdos12AllParts.all_parts`; `PrizeTarget.all_parts` | The independent statement repeats the literal mathematical predicates and operators. Its exported statement and constants match the trusted challenge. |
| The witness set in the density strengthening may depend on c. | `Erdos12AllParts.parameterwise_dense` | For every 0<c<1, a set and onset exist; no exchange to one set for all c is made. |
| A single absolute constant bounds every reciprocal sum. | `Erdos12AllParts.uniform_reciprocal_bound` | Includes all sets with Property P, finite or infinite; not just a bound depending on A. |
| Positive-integer convention. | `PositiveAudit.part_i_positive`, `PositiveAudit.part_ii_positive` | Removing zero preserves infinitude, Property P, and every counted interval. The bridge is actually compiled, and its transitive axioms are audited. For (iii), restriction to positive sets follows directly from the stronger natural-number statement. |

The literal [Submission.lean](../Submission.lean) statement was independently
written from the original questions; it does not define the desired statement
as an alias for the theorem being checked. The template [Challenge.lean](../Challenge.lean)
imports only Mathlib and was built separately. Its intentional placeholder is
never imported by the solution and is not used as a proof. The compiled source
contains no new axioms, `sorry`, `admit`, native decision calls, kernel-skip
settings, unsafe declarations, or environment initialization code; the
[static scan](static-scan.json) supplements the transitive audits rather than
replacing them.

## Environment and actual execution

- Lean: 4.35.0-rc2; Lake: the version reported in [versions.log](logs/versions.log).
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`. All nine dependency
  checkout revisions match `lake-manifest.json` with no tracked changes.
  See [dependencies.json](dependencies.json) and [toolchain-binaries.json](toolchain-binaries.json).
- Platform: macOS, arm64. Each submitted-code process ran under a native
  `sandbox-exec` profile with networking denied, user-file reads restricted,
  and writes confined to the audit directory. HOME and environment were
  cleared/replaced for execution. [Isolation probes](logs/isolation-2.log)
  confirmed outside-file reads, outside-file writes, and network access were
  denied. This was not merely a temporary working directory.
- Resource settings: two Lean worker threads, 8192 MiB for direct source
  compilation, 1800 seconds CPU limit per process, 2 GiB output-file limit,
  and 1024 file descriptors. Nanoda used the comparator's four-thread setting.
- Trusted dependency caches were reused read-only. The submitted source was
  compiled afresh; no submitter-provided `.olean` was accepted in place of
  that compilation. A normal Lake rebuild was not used as the final result:
  machine-specific dependency trace metadata caused unnecessary dependency
  rebuilds. The published direct-compiler build script avoids that issue.

| Check | Actual command, inside the restricted environment | Exit | Time |
| --- | --- | --- | --- |
| Fresh source, six public declarations, and literal bridge | `sh scripts/check.sh` | 0 | 122.54 s |
| Kernel replay of the combined development | `lake env leanchecker Erdos12AllParts` | 0 | 61.106 s |
| Positive-integer bridge | `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false PositiveBridge.lean` | 0 | 7.983 s |
| Independent statement, allowed axioms, Nanoda and default-kernel checks | export-and-compare script | 0 | 393.226 s |

[execution.jsonl](execution.jsonl) records the actual commands, working
directories, return codes, and timings. [source-build.log](logs/source-build.log)
contains the printed types, proof terms, and axiom lists. The standalone
workflow helper's [preflight](preflight.json) passed; the module, source, and
axiom stages were executed directly using the published scripts, not reported
as a run of the automated driver. No diagnostic repair was made to the selected
proof source. The additional positive-integer bridge is an audit harness.

## Independent checker and exporter details

The comparator accepted `PrizeTarget.all_parts` against the independently
compiled literal challenge. It checked equality of the statement and all
relevant constants, the allowed-axiom closure, and the exported solution with
both Nanoda and Lean's default kernel. See [comparator-final.log](logs/comparator-final.log).

On macOS, the Linux `bwrap` wrapper is unavailable. The comparator's built-in
sandbox was disabled **inside the already restricted native macOS sandbox**.
Its generic warning refers to the inner wrapper; the actual outer isolation
and probes are recorded above. The exports were generated in that restricted
process from the selected source and compiled objects. No arbitrary third-party
export was substituted.

The export list includes the primitive and quotient constants required by
`primitiveTargets` and `builtinTargets` in this pinned Lake version. An initial
minimal-export diagnostic omitted `String.mk` and could not run the comparison;
this exporter configuration was corrected without changing either theorem
statement or the proof. The successful check used the complete built-in list.

[export-hashes.json](export-hashes.json) identifies the generated NDJSON exports.
These large reproducible intermediate files are retained locally, not committed;
[export-and-compare.sh](export-and-compare.sh) regenerates them. The originally
executed command file is [executed-export-and-compare.sh](executed-export-and-compare.sh).

## Trust dependencies and result

All six public targets, the literal three-question bridge, and the two
positive-integer targets report exactly the standard Lean foundations:

```text
[propext, Classical.choice, Quot.sound]
```

No target depends on `sorryAx`, a native-evaluation axiom, or a custom unproved
assumption. The statement is closed rather than conditional on its own
conclusion. The source includes the actual part-(iii) proof and attributed
proofs for (i) and (ii), not imported placeholder catalog theorems.

**Completed levels:** source and semantic review; actual fresh Lean execution;
transitive axiom inspection; kernel replay; independent challenge comparison;
Nanoda external checking of the exported solution; fresh default-kernel
checking of that export. The result establishes formal completeness for the
specified statements within the stated Lean/Mathlib foundations.

**Limits:** this is not independent human mathematical peer review. No Linux CI
run, prize-maintainer verification, authorship/identity investigation, priority
adjudication, claim approval, or award decision is asserted. Those remain
separate review steps. The supplied paper is the team's mathematical evidence
for that review; source publication and a self-check do not themselves award a
prize.
