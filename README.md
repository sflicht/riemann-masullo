# RiemannMasullo

A Lean 4 formalization of Alessandro Maria Masullo's *The Music of the Primes* (940 pp.), built
in the open by people and their coding agents.

**[Progress map](https://claude.ai/artifact/CtQyX8qfYAF822bgHJHHE3)**: every section of the
paper, what is stated in Lean, what is open as an issue, and what is proved, with the
dependencies between them. It is refreshed about every 20 minutes.

## What this project is for

The paper claims the generalized Riemann hypothesis for the Hecke L-functions of every number
field. It is an unrefereed draft, and its author says it is unfinished. We are formalizing it
from the ground up, as faithfully as we can: each definition and statement goes into Lean as the
paper prints it, with its page number, and every place where the Lean differs from the print is
marked as a deviation.

The aim, in this order:

1. **Formalize as much as possible.** State the paper in Lean section by section, and prove what
   is stated.
2. **Repair as much as possible.** Where a statement is false or a proof does not work, find the
   statement that is true and still does the job the paper needs from it, and prove that. The
   printed claim is kept in Lean as a proposition, together with a proof that it is false.
3. **Identify clearly whatever gaps remain.** What can be neither proved nor repaired is
   recorded exactly: the page, what is claimed, and what is missing. In the Lean it is a named
   statement left unproved, with everything else proved around it, so that it is plain what
   rests on each gap.

Every gap or problem found on the way is logged in [`ERRATA.md`](ERRATA.md), each compared with
the printed page. The project does not assume that the paper's main claim is right, and it does
not assume that it is wrong. Its result, whatever becomes of the main theorem, is a
machine-checked account of which parts of the paper hold, which hold after repair, and which do
not.

## Get involved

**What is left is open to everyone at once.** The formalization is close to its end, and the
work now is to find repairs for the last gaps in the proof. Each open step is an issue labelled
[`open-problem`](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Aopen-problem), and [What is left: the open problems](https://github.com/mccorvie/riemann-masullo/issues/7349) lists them all: four
the one statement on which the whole proof rests in Lean, further statements that are in Lean
without a proof, proof steps that the manuscript does not state precisely enough to formalize,
and known theorems that have no formal proof here.

These issues are **not claimed**. Nobody holds one, several people can work on the same one, and
a partial result posted on the issue is a contribution: a sketch, a reference, a weaker
statement that the later pages can use, a counterexample. So is a reduction of a step to a
classical or known result, ideally with a citation, even without a proof of that result.
Nobody here knows whether these steps
can be repaired. That is what there is to find out.

You need no special access. Give your coding agent (Codex, Claude Code or any agent that can run
shell commands) this instruction, with the number of the issue you want it to work on:

> Help repair a gap in a mathematics paper that has been formalized in Lean 4. Fork and clone
> the repository with `gh repo fork mccorvie/riemann-masullo --clone`, run `lake exe cache get`
> in it, then read `AGENTS.md`, `prompts/prover.md` and the section "Working efficiently" of
> `CONTRIBUTING.md`. Work on issue #N, which is labelled `open-problem`. It is not claimed and
> others may be working on it too: do not comment `Claiming`. Read the issue and all its
> comments, the row of `ERRATA.md` it names, and the pages of the paper
> (`scripts/paper.sh <first> <last>`), and find out what is already known: what has been tried,
> and what the library proves around the step. Then try, in this order. If the issue has a Lean
> statement, prove it as written. If that is out of reach, prove it from one or two smaller
> precise statements, each written in Lean, so that it is plain what is still missing. (For
> the one statement that the target theorems rest on, #5571, such a proof does not replace it:
> put the new statements and the implication in the section's isolation file, as `AGENTS.md`
> says.) A
> reduction to a classical or known result is welcome even if you do not prove that result:
> state it as a lemma of its own with `sorry`, begin its docstring with `Classical input:`, and
> cite it, ideally with the item and page of the source. If the
> step has no Lean statement, write the statement the later pages need and prove it. If the
> step is false, give a counterexample, best of all as a Lean proof of the negation. Never
> change a statement that is on `main`: propose the change on the issue. Use nothing from any
> formalization of the Riemann hypothesis released in November 2026, and nothing derived from
> one: this project tests the route of this paper, and such a pull request is not merged. While
> you work, build only the file you are in (`lake build RiemannMasullo.<Chapter>.<File>`). At
> the end run `lake build RiemannMasullo Challenge Main` and `scripts/lint.sh`. If you have
> Lean to hand in, open a pull request against `main` and link it on the issue. If you have
> mathematics and no Lean, post it on the issue: the paper item and page, what you claim, and
> the argument or the reference. If you got nowhere, say on the issue what you tried and where
> it stopped, so that the next person starts further on.

Doing it by hand works the same way, and mathematics without Lean is welcome on the issues: a
sketch is enough for others to work from. (A fork is needed because GitHub only lets
collaborators push branches to this repository; your pull request comes from your copy.) Every
pull request is built and checked automatically, and then read by the project before it
merges: since 24 November 2026 nothing is merged automatically. [`CONTRIBUTING.md`](CONTRIBUTING.md) has the details, and what
we have learned about doing this quickly.

A few statements of the supplementary chapters are still open as ordinary
[`proof` issues](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Aproof+label%3Asupplementary+-label%3Aclaimed).
Those are taken one person at a time: comment `Claiming` on one to take it, and `Releasing` to
give it back.

## Status

**Searching for repairs of the final gaps in the proof.** As of 24 November 2026, about 13,200
theorems and 1,800 definitions are stated in Lean. In the chapters the trace formula rests on
(Chapters 2–7 and 9–13, with Appendices A–D) all but fifteen of the theorems are proved. About ninety people have
had pull requests merged, some 2,660 pull requests in all.

- **Those chapters are stated, and what could be proved is proved.** Where a
  printed argument did not work, the statement was repaired or proved by another route, and
  [`ERRATA.md`](ERRATA.md) records it.
- **One gap on the main line: all seven target theorems rest on one statement.** In Lean the paper's main claim, and the
  theorems for Dedekind zeta functions, Dirichlet L-functions and the Riemann zeta function
  that are derived from it, use exactly one statement that has no proof: the cancellation of
  the zeros outside the strip in Theorem 12.5.1.1. It is proved in Lean that this cancellation,
  for every width, is equivalent to the main claim, so nothing weaker can supply it.
- **Nine more open statements, off the main line.** Each is a named Lean statement, neither
  proved nor refuted, and the Lean proof of the targets uses none of them. Five, under the
  bases and traces of Chapters 7 and 10, are statements from which other theorems of the paper
  are proved. Four, under §10.3, §10.4 and (12.5.1.4), are used by nothing else in Lean and are
  not known to hold; they are kept in files that nothing imports.
- **Five proof steps that the manuscript does not state precisely enough to formalize,** in
  Chapters 7, 11 and 12. They have no Lean statement.
- **Five classical inputs:** theorems of the literature that are stated in Lean and used, and
  not proved there. The targets do not use them either.
- **290 statements of the manuscript are proved false as printed.** Each is kept in Lean with
  a machine-checked proof of its negation, next to the corrected statement, which is proved.
  Six more such proofs rest on a statement that is itself still open.
- The supplementary material (Chapters 8 and 14, Appendix E, §A.4, §B.7), on which the trace
  formula does not rest, is partly stated and proved, and is not being worked on.

All of these are listed in [What is left: the open problems](https://github.com/mccorvie/riemann-masullo/issues/7349). The
[progress map](https://claude.ai/artifact/CtQyX8qfYAF822bgHJHHE3) has the current numbers.

### What the formalization has found

[`ERRATA.md`](ERRATA.md) has about 790 entries: some 280 statements that are false as printed,
430 that are imprecise, inconsistent or wrongly justified, 50 placeholders or missing pieces,
and 30 reports about parts of the paper that are not stated in Lean. Five outside audits have
been compared with it report by report, and it names them where they found the same thing. Those in the appendices' and early
chapters' accounts of standard material are repaired where they occur: the Lean states the
corrected form and says so.

Most findings in the paper's own constructions, in Chapters 5–7 and 10–12, also come with a
repair. Twenty-eight steps had none when they were found, and later results use them;
`ERRATA.md` lists them first. Sixteen of the twenty-eight have since been proved in Lean: by an
argument that is not the paper's, from another of the steps, or, in one case, from a published
theorem that is taken as known. Among them are the structure theorem for the spaces of adelic
θ-functions (Theorem 5.2.1.1), the reverse inclusion of the global converse theorem (Theorem
6.3.2.1) and the spectral and orbital Markushevich bases (§10.2, §11.2). `ERRATA.md` says for
each by which route. The explicit formula of §B.4, which Chapter 12 quotes, is proved in full,
with its local terms and normalizations recomputed.

Twelve steps remain open, all in Chapters 7 and 10–12: the separate convergence in Theorem
7.1.2.3 and the Paley–Wiener orbital bases of Theorem 7.3.3.4, which meet the same arithmetic
question; the normalized bases and the trace-norm estimates of §10.2–10.4; the lifts of
(11.3.1.3)–(11.3.1.4); and the steps of Chapter 12 that lead to the trace formula, where the
section that should compare the global trace with the S-local one (§12.3) consists of its
heading and a note to include it. These are the assessments of the agents that checked the
entries against the pages, not a specialist's. Each open step is one of the
[open problems](https://github.com/mccorvie/riemann-masullo/issues/7349).

### Concerns about the main theorem

Separately from this project, concerns have been raised about gaps in the proof of the paper's
main theorem, the trace formula of Theorem 12.5.1.1. They come from readings of the paper
discussed in the Lean Zulip thread
[Formalising Masullo's proof of GRH](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Formalising.20Masullo.27s.20proof.20of.20GRH/with/642314625),
where the details were not posted at first. They did not come from this formalization, which
had not then reached that part of the paper; what it has found there since is described above,
and written accounts of several of those readings are listed under
[Acknowledgments](#acknowledgments). John Baez's post
[*Masullo on the Riemann Hypothesis*](https://johncarlosbaez.wordpress.com/2026/11/22/masullo-on-the-riemann-hypothesis/)
sketches the strategy of the paper for a general reader and describes two of the reported
problems. The draft is also unfinished by its author's own account:
Chapter 13, which should deduce GRH from the trace formula, does not yet state its main theorem.

This is what the three aims above are for: when the formalization reaches a part that does not
hold as printed, the work is to repair it if it can be repaired, and otherwise to write down
the gap exactly. [`CONTRIBUTING.md`](CONTRIBUTING.md#when-the-paper-is-wrong) says how each
case is recorded. The prerequisites (adeles and ideles, Haar measures, locally convex and
nuclear spaces, Schwartz–Bruhat functions) are standard mathematics worth having in Lean
whatever becomes of the main theorem.

## The paper

The manuscript is in [`paper/`](paper/) (PDF plus a `pdftotext -layout` extraction for search),
and [`transcription/`](transcription/README.md) has a Markdown transcription with the formulas
in LaTeX, contributed by [@aadrianvv](https://github.com/aadrianvv): a reading aid, checked
against the PDF but not an exact copy. The PDF decides.

## Layout

The library mirrors the paper's table of contents. Each chapter or appendix has an index file,
and its sections go in a directory of the same name (`RiemannMasullo/Ch02_AdelicTheta/Sec1.lean`):

| File | Paper |
|---|---|
| `RiemannMasullo/Ch02_AdelicTheta.lean` | Ch. 2 Adelic θ-functions |
| `RiemannMasullo/Ch03_IdelicZeta.lean` | Ch. 3 Idelic Zeta Functions |
| `RiemannMasullo/Ch04_PeriodicSchauderBases.lean` | Ch. 4 Periodic Schauder Bases on modulated groups |
| `RiemannMasullo/Ch05_ThetaZSpaces.lean` | Ch. 5 Spaces of adelic θ-functions and Idelic Z-functions |
| `RiemannMasullo/Ch06_LocalGlobal.lean` | Ch. 6 Local-Global structures |
| `RiemannMasullo/Ch07_SchauderBasesZeta.lean` | Ch. 7 Schauder Bases of Idelic Zeta functions |
| `RiemannMasullo/Ch08_PeriodicOrbits.lean` | Ch. 8 Periodic Orbits and Fixed Points |
| `RiemannMasullo/Ch09_HardySobolev.lean` | Ch. 9 Hardy-Sobolev topologies |
| `RiemannMasullo/Ch10_TraceSpectral.lean` | Ch. 10 Trace formula: Spectral Side |
| `RiemannMasullo/Ch11_ShellStructure.lean` | Ch. 11 The Shell Structure |
| `RiemannMasullo/Ch12_TraceGeometric.lean` | Ch. 12 Trace formula: Geometric Side |
| `RiemannMasullo/Ch13_ZerosHecke.lean` | Ch. 13 Zeros of Hecke L-functions |
| `RiemannMasullo/Ch14_Complements.lean` | Ch. 14 Complements |
| `RiemannMasullo/AppA_AlgebraicNT.lean` | App. A Algebraic Number Theory |
| `RiemannMasullo/AppB_AnalyticNT.lean` | App. B Analytic Number Theory |
| `RiemannMasullo/AppC_LCTVS.lean` | App. C Locally convex TVS |
| `RiemannMasullo/AppD_SchwartzBruhat.lean` | App. D Schwartz-Bruhat functions |
| `RiemannMasullo/AppE_TopologicalStacks.lean` | App. E Topological stacks |

(Chapter 1 is the informal introduction and has no file.)

Third-party formalizations we build on are vendored under
[`RiemannMasullo/External/`](RiemannMasullo/External/README.md), with credits in
[`ATTRIBUTION.md`](RiemannMasullo/External/ATTRIBUTION.md). Class field theory comes from a Lake
dependency and is used in a library of its own, [`RiemannMasulloClassField/`](RiemannMasulloClassField/README.md).

## Roadmap

The order follows the paper's own cross-references. Two streams run in parallel and meet at the
trace formula:

| Wave | Paper | Status |
|---|---|---|
| 1 | Appendices A.1–A.3, A.5, C, D; then Chapters 2–3 (adelic θ-functions, idelic zeta functions) and, independently, Chapters 4 and 9 (periodic Schauder bases, Hardy–Sobolev spaces) | stated and proved |
| 2 | Chapters 5–7, with Appendix B.1–B.6 | stated; proved except for the open steps of Chapter 7 ([open problems](https://github.com/mccorvie/riemann-masullo/issues/7349)) and one classical input in Chapter 5 |
| 3 | Chapters 10–12: the trace formula; then Chapter 13 | stated; proved except for the open steps of Chapters 10–12 ([open problems](https://github.com/mccorvie/riemann-masullo/issues/7349)) |
| later | Chapters 8 and 14, Appendix E, A.4, B.7 | partly stated and proved; the trace formula does not rest on them |

An issue labelled `blocked` is waiting for the sections it builds on. The appendices are mostly
standard mathematics, and several pieces already exist in other Lean projects (see
[issue #3](https://github.com/mccorvie/riemann-masullo/issues/3)); the chapters are where the
paper's own argument is tested.

## How the work is organized

Work goes through issues and pull requests: scouts find existing Lean, digesters turn paper
sections into statements, reviewers compare those statements with the paper, provers and
sweepers close the `sorry`s, and an integrator and a merger review and merge. Start with
[`CONTRIBUTING.md`](CONTRIBUTING.md); the rules every contribution follows are in
[`AGENTS.md`](AGENTS.md), and the role prompts in [`prompts/`](prompts/README.md).

## Building

```sh
lake exe cache get                          # download prebuilt Mathlib
lake build RiemannMasullo Challenge Main    # the library and the target theorems
lake build                                  # everything, with the class field theory library
```

The plain `lake build` also compiles the class field theory dependency, once (about five hours
of one processor core).

Pinned to Lean `v4.36.0` / Mathlib `v4.36.0`.

## Comparator

The target statements are checked with [Comparator](https://github.com/leanprover/comparator)
(`lake comparator`, built into Lean from 4.35), following the setup for Alpoge's formalization at
<https://github.com/Deicyde/riemann-hypothesis>.

| File | What it is |
|---|---|
| [`Statements.lean`](Statements.lean) | definitions of the target statements; imports only Mathlib |
| [`Challenge.lean`](Challenge.lean) | the theorems, with `sorry` |
| [`Main.lean`](Main.lean) | the same theorems, each obtained from `RiemannMasullo` |
| [`comparator.json`](comparator.json) | the Comparator config |

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive` | RH and GRH for Dirichlet L-functions, identical to the Alpoge challenge |
| `dedekindZeta_zeros_re` | GRH for the Dedekind zeta function of every number field |
| `heckeLFunction_zeros_re` | GRH for `L(s, χ)`, every number field, every unitary Hecke character |

```sh
lake comparator              # needs bubblewrap; add --paranoid for the extra kernels
```

It currently rejects with `Illegal axiom detected: 'sorryAx'`, as it should for as long as anything
the proofs rest on is open.

`Main.lean` no longer contains a `sorry` of its own. Each of the seven theorems is one line that
appeals to the library, and the route from there back to the paper is explicit:

| Step | Where | State |
|---|---|---|
| The seven targets from the paper's main claim: translation to Mathlib's Hecke characters, and the classical reductions (Hecke to Dedekind to zeta, and to Dirichlet characters) | [`Ch13_ZerosHecke/Targets.lean`](RiemannMasullo/Ch13_ZerosHecke/Targets.lean) | proved from the main claim; nothing else is open beneath them |
| The paper's main claim, `heckeL_zero_re_eq_half`: for every number field and every unitary character of its idele class group, the zeros of the completed Hecke L-function in the open critical strip lie on the line | [`Ch01_Introduction/Sec4.lean`](RiemannMasullo/Ch01_Introduction/Sec4.lean) | derived in Lean from the steps of §1.4 of the paper |
| The steps of §1.4: the family of test functions, the uniform bound and Montel's theorem, the logarithmic derivative, the functional equation | the same file, and `Sec4_Printed.lean` | the uniform bound of §1.4.3 is false as printed (the objection raised by Jenny Lorraine Nielsen, confirmed here with a counterexample for the trivial rational character); the holomorphic extension that §1.4.5 needs is proved from the cancellation in Theorem 12.5.1.1 |
| The trace formula, Theorem 12.5.1.1 | [`Ch12_TraceGeometric/Sec5.lean`](RiemannMasullo/Ch12_TraceGeometric/Sec5.lean) | stated in corrected form; its open step, the cancellation of the zeros outside the strip, is the recorded gap `traceFormula_exteriorZeros` ([#5571](https://github.com/mccorvie/riemann-masullo/issues/5571)), on which all seven targets rest, and on nothing else that is open |

The paper has no numbered statement of its main theorem: Theorem 13.3.1.2 is a title in the
current draft, and the claim is argued in the introduction (§1.4, pp. 27–31). The two targets
beyond the Alpoge challenge, for Dedekind zeta functions and for Hecke L-functions, were written
from that introduction; a reviewer has since checked that the bridge proves them at exactly
their Comparator types.

## Acknowledgments

The pull requests and issues show who stated, proved and reported what. The project also rests
on work that does not appear there.

- **Alessandro Maria Masullo** wrote the manuscript and asked readers to check and formalize it.
- **Aadrian** ([@aadrianvv](https://github.com/aadrianvv)) made the Markdown transcription in
  [`transcription/`](transcription/README.md). Every agent and contributor reads the paper
  through it.
- **Neal Patel** is formalizing parts of the same paper on his own, in
  [`thatnealpatel/grh`](https://github.com/thatnealpatel/grh) (MIT). Three proofs of the
  explicit-formula appendix here are adapted from his code, as
  [`ATTRIBUTION.md`](RiemannMasullo/External/ATTRIBUTION.md) records, and a survey of his
  repository pointed the way to further proofs and to witnesses over ℚ for refutations of
  printed claims.
- Five independent readings of the paper located gaps, some of them before the formalization
  reached those pages. [`ERRATA.md`](ERRATA.md) names them where an entry agrees with one or
  started from one, and agents that work on those pages are given them as leads to test.
  [`OUTSIDE_REPORTS.md`](OUTSIDE_REPORTS.md) indexes what each of them reported, page by page,
  with where it stands in the errata and in the Lean.
  - **Isaac Yonemoto**'s dependency audit,
    [`ityonemo/music-of-primes`](https://github.com/ityonemo/music-of-primes). It includes
    **Jenny Lorraine Nielsen**'s note *A Failure of Uniform Boundedness in Masullo's Proposed
    Proof of the Generalized Riemann Hypothesis*.
  - The [*Report on The Music of the Primes*](https://github.com/Refine-Technologies-Inc/music-of-primes-report-by-refine)
    by **Ben Golub** and Refine Technologies.
  - The companion [*Further repairs, attempted closures, and the remaining estimate*](https://anayebi.github.io/human_grh_unresolved.pdf),
    published by **Aran Nayebi**.
  - **Dev Goyal**'s audit, [`dvgyl/masullo-grh-proof-audit`](https://github.com/dvgyl/masullo-grh-proof-audit):
    a preprint, a detailed report and exact-arithmetic checks, with explicit counterexamples to
    theorems and proof steps of Chapters 6–12.
  - **Eric Naslund**'s review, [`enaslund/rh-verification`](https://github.com/enaslund/rh-verification):
    three reports on the trace argument of Chapters 11–12, among them a test of Theorem
    11.3.2.1 at the prime 2.
- **dga471** proved four of this project's statements on [Prove2Me](https://prove2.me), and
  the proofs were brought in from there.
- **Maarten Derickx** ([@koffie](https://github.com/koffie)) found why some trivial proofs never
  finished: type synonyms declared as abbreviations, whose instance terms grow exponentially
  when they are nested. He measured every one in the library and proposed the redesign (#5398)
  and the rules for new definitions (#5362), which are adapted from
  [Tau Ceti](https://github.com/TauCetiProject/TauCetiReview)'s review rubric.
- **Cornelius Roemer** ([@corneliusroemer](https://github.com/corneliusroemer)) analysed why
  the checks and the merge queue fell behind, proposed a staged plan to relieve them (#6787),
  offered a dedicated machine for it, and wrote a scheduler for the pull-request checks (#6834).
- Proofs were adapted from [`CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB) and
  [`Rogerhu12/hecke-seven-eighths`](https://github.com/Rogerhu12/hecke-seven-eighths). The
  scouts' surveys of what already exists in Lean
  ([`SURVEY.md`](RiemannMasullo/External/SURVEY.md)) drew on those and on
  `algebraic-number-theory-lean` and `quadratic-forms-lean` (jonhanke), `FLT`
  (ImperialCollegeLondon), `ideles-journal` (mariainesdff), `DedekindZetaZeroFree` (AxiomMath),
  `PrimeNumberTheoremAnd` (AlexKontorovich), `gaussian-field` (mrdouglasny) and `carleson`
  (fpvandoorn).
- Everything here is built on [Mathlib](https://github.com/leanprover-community/mathlib4), and
  much of the discussion happens in the Lean Zulip thread linked above.

If your work is used here and is missing from this list, please open an issue.

## License

The Lean code and everything else written for this project is released under the
[Apache License 2.0](LICENSE), the license of Mathlib. The manuscript in [`paper/`](paper/README.md)
belongs to its author and is not covered by it. Code vendored under `RiemannMasullo/External/`
keeps its own license and notices.
