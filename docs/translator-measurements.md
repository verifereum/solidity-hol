# Translator branch-growth measurements

Joining successful checked/calling branches keeps the remaining shallow
computation in one continuation. At four branches, main-definition size drops
from 701 to 184 nodes for checked arithmetic and from 401 to 104 for calls.
Kernel work falls from 4,556,667 to 2,071,791 primitive inferences and from
10,347,514 to 7,922,199 respectively.

The elapsed-time change is much smaller: four-branch medians are
24.361→22.352 seconds for checked arithmetic and 35.938→34.743 seconds for
calls. These shared-host timings do not establish a general speedup. The
one-branch controls have identical term sizes and inference counts but different
median times; their ranges overlap. Proof cost still grows rapidly with branch
count, even though joined definition sizes have constant increments in these
four fixtures. This is not a linear-proof-cost result.

## Method

The comparison uses clean commits [baseline `590df81`](https://github.com/verifereum/solidity-hol/commit/590df81dd1d42147b473f758e45153e092035571)
and [joined `7cda002`](https://github.com/verifereum/solidity-hol/commit/7cda0027c8dad54f816a96ed5ab2f009930ad1b7).
Their source diff is only the branch-joining change in
`translator/solidityTranslateLib.sml`: both use the same production translator,
tuple-continuation proof repair, fixture and dependency pins.

Each worktree was warmed with `holbuild -j1 buildhol`, then
`holbuild -j2 build solidityTranslatorCorpusTheory`. Each measured invocation is
a fresh HOL process:

```sh
TRANSLATOR_GROWTH_N=N TRANSLATOR_GROWTH_MODE=MODE \
  holbuild -j1 run tools/translator_growth.sml
```

`N` is 1–4 and `MODE` is `checked` or `calling`. For each pair, three repetitions
alternate baseline/joined, joined/baseline, baseline/joined. Attempts that waited
for the shared build budget were discarded and repeated. The tables show all
accepted samples as median and minimum–maximum; raw values and per-sample system
load are in [translator-measurements.csv](translator-measurements.csv).

After 45 accepted samples, a busy build queue repeatedly delayed the remaining
invocations. The last three therefore ran as sequential children of one
budgeted batch holding one job. Each sample still used the same fresh HOL
invocation; the idle batch parent and its initial queue wait were outside every
measured interval. No accepted sample includes a per-invocation budget wait.

The fixture updates one `uint8` local in each branch, either with checked
addition or a call to a checked-addition callee. Every generated core program
passes `wf_core_program`, and both functions must produce correspondence proofs.
The source unit supplies names only: this synthetic benchmark makes no claim
that its core was elaborated from that unit.

The measured interval includes generation and proof of the whole unit, including
the common callee. It excludes HOL startup, library loading and the core check.
Term size counts the syntax-tree nodes of the generated main definition's right
hand side. Kernel work is HOL's primitive-inference counter for the measured
interval. All accepted samples report zero new axioms.

The host was shared with other builds. Interleaving and recorded load limit that
confound; elapsed time remains a shared-host observation, not a controlled
single-process benchmark. Term size and primitive counts are identical across
each set of three repetitions.

The measured proof engine is the public prototype at `c42bd8d`, migrated to the
consolidated semantics and with the same tuple-continuation proof repair on both
sides. The delivery branch subsequently integrates public prototype `cf3a867`'s
proof and corpus-test repairs. Its complete-corpus validation is separate from
this frozen comparison; these numbers refer only to the two named commits.

## Checked branches

| N | Generator | Main term nodes | Kernel primitives | Seconds, median [min–max] |
|---:|:---|---:|---:|---:|
| 1 | baseline | 43 | 161,904 | 1.084 [0.905–1.171] |
| 1 | joined | 43 | 161,904 | 0.920 [0.902–0.988] |
| 2 | baseline | 137 | 682,118 | 2.931 [2.655–2.934] |
| 2 | joined | 90 | 403,450 | 2.498 [2.378–2.666] |
| 3 | baseline | 325 | 1,861,203 | 8.863 [8.226–9.327] |
| 3 | joined | 137 | 894,908 | 7.665 [7.107–7.958] |
| 4 | baseline | 701 | 4,556,667 | 24.361 [24.361–24.659] |
| 4 | joined | 184 | 2,071,791 | 22.352 [21.997–22.934] |

## Calling branches

| N | Generator | Main term nodes | Kernel primitives | Seconds, median [min–max] |
|---:|:---|---:|---:|---:|
| 1 | baseline | 23 | 815,326 | 1.586 [1.576–1.872] |
| 1 | joined | 23 | 815,326 | 1.834 [1.804–1.841] |
| 2 | baseline | 77 | 2,014,202 | 4.528 [4.268–4.570] |
| 2 | joined | 50 | 1,738,317 | 4.035 [3.890–4.410] |
| 3 | baseline | 185 | 4,611,643 | 12.565 [12.308–12.896] |
| 3 | joined | 77 | 3,661,533 | 11.703 [11.386–11.749] |
| 4 | baseline | 401 | 10,347,514 | 35.938 [35.708–37.731] |
| 4 | joined | 104 | 7,922,199 | 34.743 [34.432–35.682] |

Accepted-sample one-minute system load: 4.94–13.88 on 32 logical CPUs.
