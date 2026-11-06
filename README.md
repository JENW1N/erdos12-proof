# Erdős Problem 12 — all three numbered parts

Mathematical manuscript and complete Lean formalization submitted for review
under **JSP-000051** of The Justin Sun Prize.

The three answers are **yes, no, yes**. The new contribution presented for
review is the proof of part (iii), including an absolute bound on the reciprocal
sum. Parts (i) and (ii) are prior results of Google DeepMind / AlphaProof Nexus;
this repository includes attributed adaptations to give complete coverage of
the three numbered questions. Integration does not transfer their authorship
or establish a new priority claim to those prior results.

## Authors and roles

The part-(iii) manuscript and supplied proof project are by **Will Howe, Grant
Huffman, Jensen Kohlmeyer, and Liam Kruer**. The same team submits this integrated
account. The submission is made from Jensen Kohlmeyer's account, `JENW1N`.
See [AUTHORS.md](AUTHORS.md) and [NOTICE.md](NOTICE.md) for the contribution record,
AI assistance, and retained upstream attribution. Identity and individual
contributions remain subject to the prize's review.

## Read the result

- [Mathematical paper (PDF)](paper/erdos12-all-parts.pdf), November 5, 2026, 16 pages.
- [Single-file Lean proof](Erdos12AllParts.lean), importing only Mathlib.
- [Editable paper source](paper/main.tex).
- [Prior-source records](provenance/alphaproof-nexus.json).

The PDF states the answers in Theorems 1.1–1.3. Section 2 proves the two counting
results using the released AlphaProof Nexus constructions. Sections 3–9 give the
reciprocal-sum proof. Section 10 records formalization provenance. The original
part-(iii) technical sections and the embedded 201-module proof closure are
retained unchanged.

## Formal entry points

All names below are in namespace `Erdos12AllParts`.

| Declaration | Statement |
| --- | --- |
| `part_i` | Some infinite good set has positive square-root-normalized lower limit. |
| `part_ii` | No positive exponent saving works infinitely often for every infinite good set. |
| `part_iii` | Every infinite good set has a convergent reciprocal sum. |
| `all_parts` | The conjunction of these three answers. |
| `parameterwise_dense` | For each exponent in (0,1), an exponent-dependent good set eventually meets the corresponding power lower bound. |
| `uniform_reciprocal_bound` | A single constant bounds the reciprocal sum for every set with Property P, including finite sets. |

Here Property P forbids three distinct elements a,b,c with a<b, a<c and a
 dividing b+c. Equal larger summands are permitted. The counting functions use
A intersected with {1,...,N}. Lean's natural numbers include zero and its real
reciprocal of zero is zero; deletion of zero preserves infinitude, Property P,
and all these counting functions. The original positive-integer statement is
therefore covered. The dense set in part (ii) depends on its exponent.

## Reproduce

The toolchain is **Lean 4.35.0-rc2**. Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; all transitive revisions are in
[lake-manifest.json](lake-manifest.json). Install Elan from its official source,
clone this repository, and check out the full commit named in the prize PR.
Then run:

```sh
lake exe cache get
./scripts/check.sh
```

`scripts/check.sh` builds the submitted source directly against the pinned
dependency environment, then checks the audit and statement bridge. It avoids
rebuilding unchanged Mathlib modules merely because cache traces differ between
machines. The conventional `lake build` is also available.

`Audit.lean` prints all six public theorem types, proof terms, and complete
transitive axiom lists. `Submission.lean` proves a separately written literal
statement of all three questions, for statement comparison. `Challenge.lean`
is the independent statement template for `lake comparator`; its deliberate
placeholder is never imported by the proof or default build. It is not evidence
of a proved theorem. Only the submitted solution is used as the proof.

The checked proof endpoints depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The prize PR links a fixed-version verification report and actual
build/checker logs. A local self-check is not organizer acceptance or peer review.

To render the paper, run `tectonic main.tex` from `paper/`.

## Review and submission status

This repository publishes the authors' proof for mathematical and formal review.
It does not assert independent journal peer review, an award, or a verified
priority date earlier than its public source history. No payment or identity
verification information is included. Earlier Conjectures.io upload files and
their hash-bound chat-log archive are separate artifacts.
