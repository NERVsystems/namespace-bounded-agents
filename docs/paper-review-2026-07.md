# Pre-Submission Review: "Namespace-Bounded Agents" (main-arxiv.tex)

Reviewer pass: July 2026. Scope: full read of `paper/main-arxiv.tex` (1,783 lines,
~30 pp. single column) plus spot-checks against `evaluation/` artifacts.

**Verdict in one paragraph.** The core idea — capabilities as filesystem paths in
per-process namespaces, so cross-tool prompt injection fails with ENOENT instead of
depending on model refusal — is genuinely novel in the LLM-security literature, well
argued, and backed by an unusually broad artifact set (attack corpus, AgentDojo,
token benchmark, TLA+/SPIN/CBMC). The paper is publishable at a good venue. But in
its current form it has (a) two evaluation-integrity problems that a careful reviewer
with artifact access *will* find, (b) one glaring related-work omission (CaMeL), and
(c) roughly 25–30% redundant text. Fix those three things; resist the urge to do more.

---

## 1. Must-fix before submission (blocking)

### M1. Benign utility is unreported — and the artifacts show it is 14.4%

The paper never reports AgentDojo **utility** (benign task completion), yet
`evaluation/agentdojo/python/results/full_evaluation_20260125_153218/evaluation_minimal_flat_CORRECTED.json`
records:

```
benign_utility: 14.4%   utility_under_attack: 13.9%   ASR: 0.7%
```

Published AgentDojo baselines put Claude-class models at ~60–80% benign utility.
An agent with 14% utility is trivially "secure" — reviewers who know AgentDojo will
ask for utility in the first round, and AgentDojo's own headline metric is the
security/utility trade-off. Three possibilities, in order of likelihood:

1. The utility measurement through the namespace adapter/state bridge is broken
   (plausible given `test_state_bridge.py` exists) — then fix it and re-run;
2. Utility is genuinely low because the text/filesystem interaction format degrades
   task completion — then this must be reported and discussed honestly (it does not
   kill the paper: the structural-security claim survives, but the "parity" story in
   Table `tab:success` does not generalize);
3. The number means something else — then define and report it anyway.

**This is the single highest-priority item.** Do not submit anywhere until you know
which of the three it is.

### M2. The structural/behavioral split in Table `tab:agentdojo-results` contradicts the artifacts

The paper claims: cross-tool 473 → **Structural Block 473 (100%), Behavioral 0**.
The results JSON records `defense_breakdown: structural_blocks 188 (30.7%),
behavioral_blocks 420 (68.6%)` — i.e., in most cross-tool cases the model never
*attempted* the forbidden path, so no ENOENT was ever returned. The paper's own
definition of "structural block" (Table `tab:outcome-labels`: "ENOENT returned
before tool code executes") requires an attempt.

The claim you are entitled to is: *cross-tool attacks are **structurally
guaranteed** to fail (the capability is absent from the interface), and 0/473
succeeded; of these, N were actually attempted and blocked with ENOENT, the rest
were never attempted.* That is still a strong result — arguably stronger, because
the attempted-and-blocked subset is direct evidence the guarantee binds. Report the
real split (attempted-and-blocked vs. never-attempted) instead of relabeling
everything "structural." As written, an artifact-evaluation committee will flag
this as a data/paper mismatch.

Related: the artifact notes **17 dropped Slack tasks** ("broken security checks,
AgentDojo API mismatch", later re-run in `slack_rerun_20260128_155241`). The paper
reports 473 cross-tool without mentioning the drop/re-run. One sentence in the
appendix fixes this; silence invites accusations.

### M3. Reframe the AgentDojo cross-tool result as attack-surface analysis, not an empirical finding

Since the AgentDojo run uses a tool-visibility filter (admitted, but only in the
appendix, §A.7), the 0% cross-tool ASR is true **by construction**: attacks whose
required tool was removed cannot succeed. Presenting it in the headline results
table as if it were an empirical discovery invites the "tautology" review. The
honest and more defensible framing:

- **Empirical contributions**: (i) 75.2% of AgentDojo's 629 injections require
  capabilities outside the minimal task namespace — a measurement of how much of a
  standard benchmark's attack surface least-privilege scoping removes; (ii) the
  residual same-tool ASR is 2.6% with behavioral defense; (iii) the 31-attack corpus
  against a **real 9P server** shows GPT-4o/GPT-5 attempting attacks that the
  namespace blocks (this is your best empirical evidence — promote it).
- **Structural contribution**: the guarantee itself, backed by the formal
  verification of the actual kernel path-resolution code.

Move the "tool-visibility filter, not end-to-end 9P" disclosure from the appendix
into the main text at first mention of AgentDojo (one clear sentence suffices).
Burying it looks worse than stating it.

### M4. The minimal-namespace oracle problem, and the missing comparison to AgentDojo's own tool filter

Cross-tool/same-tool classification and namespace construction were "performed by
comparing each injection's target tools against the minimal tool set for the
corresponding user task" — i.e., the minimal namespace was derived with knowledge
of the task (and the paper hand-waves T_min as "static analysis... or explicit
policy"). Two consequences:

1. The comparison to **Progent (2.2% ASR)** is not apples-to-apples: Progent
   *automatically generates* policies; your namespaces are oracle-minimal. Either
   soften the "lower than Progent" claim or add a sentence acknowledging the
   oracle advantage.
2. The AgentDojo paper itself ships a **`tool_filter` defense** (an LLM selects the
   task-relevant tool subset before execution) with published numbers. It is the
   closest baseline to your approach and is currently uncited in the evaluation.
   You must compare against it and articulate the delta: your contribution over
   tool filtering is **enforcement level** (kernel/protocol vs. prompt-layer
   filtering that a manipulated model could circumvent in frameworks where the
   dispatcher still routes unlisted tools) **plus formal verification of the
   enforcement mechanism**. That argument is available to you and it is good — but
   the paper has to make it explicitly, or a reviewer will make it for you,
   unfavorably.

### M5. Missing related work: CaMeL (and friends)

**CaMeL** (Debenedetti et al., 2025, "Defeating Prompt Injections by Design") is
capability-based, provides by-construction guarantees, and is evaluated on
AgentDojo — the same benchmark, the same "structural not behavioral" pitch, from
the same group that built AgentDojo. Its absence is the paper's most conspicuous
related-work gap; any reviewer in this space will notice within minutes. Position
against it directly: CaMeL enforces capabilities in a custom Python interpreter at
the data-flow level; you enforce at the OS/protocol level with a 30-year-old,
formally verified primitive, no interpreter in the TCB, and per-request namespace
composition. Also worth a sentence each: IsolateGPT, Beurer-Kellner et al. 2025
("Design Patterns for Securing LLM Agents"), and the action-selector/plan-then-execute
pattern family.

### M6. Internal inconsistencies (quick fixes, but they add up)

- §"Same-Tool Attacks": "the remaining **25.5%**" → should be **24.8%** (156/629).
- Abstract and headline claim "0% ASR" on the 31-attack corpus, but Table
  `tab:security` totals **2/31** for 9P (capability-misuse successes). You do
  explain (explicit non-goal), but the raw total row contradicts the abstract on a
  skim. Split the table into in-scope (29, 0 successes) and out-of-scope (2) rows,
  and say "0% for in-scope attacks" everywhere.
- Table `tab:hardened-comparison`: hardened MCP n=93 (3 runs) vs. 9P n=124 (4 runs)
  in the same table with no explanation of the differing run counts.
- Abstract: "SPIN (131,333 states..., **0 errors**)" then "SPIN race model
  **confirms three use-after-free races**." Both true (the race model is *designed*
  to find them; the 5 protocol models pass) but reads as a contradiction. Reword:
  "5 protocol models pass; a sixth targeted model reproduces 3 known-pattern races
  in the host threading layer."
- README vs. paper: README claims AgentDojo 9P ASR **0.0%** and MCP baseline
  **37.8%**; the paper says **0.6%** and cites the published GPT-4o baseline of
  **53.1%**. Reconcile (the README overclaims relative to the paper).
- Zenodo DOI: README badge `10.5281/zenodo.18419122` vs. paper footnote
  `...18419123`. Presumably concept-vs-version DOI; make them consistent or label.
- Artifact ASR is 0.7% (4/612 scored) vs. paper's 0.6% (4/629) — pick one
  denominator and state it.

### M7. Token-efficiency claim needs a prompt-caching caveat

The 83.5% reduction rests on "MCP resends 1,430 schema tokens per call." Both
Anthropic and OpenAI now offer prompt caching that makes repeated schema tokens
nearly free (cached-input pricing ~10% of base), and in multi-turn conversations
the namespace listing is also resent as history. The *relative* point survives
(shorter context, less attack-relevant surface, fewer distinct tokens to poison),
but the headline 83.5% will draw a "have you heard of prompt caching?" review.
Add one caveat paragraph: report the comparison with and without caching assumptions,
or reframe as context-length/attack-surface reduction rather than cost reduction.

---

## 2. Should-fix (non-blocking but will strengthen review outcomes)

- **"Theorem 1" is not a theorem.** It is a security claim with four assumptions
  and an informal argument, typeset inside a table float. Formal-methods reviewers
  are allergic to this. Rename ("Security Claim 1" or "Guarantee 1"), move out of
  the float, and point to the machine-checked TLA+ theorem as the formal object.
- **Tone down absolutes**: "Injection Immunity" (Property 2), "Jailbreak safe:
  Yes" (Table `tab:comparative`), "Semantic attack elimination" (conclusion).
  Each is qualified elsewhere, but the unqualified labels are what reviewers
  quote. "Cross-tool injection immunity", "jailbreak-resilient for cross-tool
  access", "semantic→syntactic transformation" are defensible; the absolutes are not.
- **Weak incident sourcing**: the Claude CLI (HN, unconfirmed) and Replit
  (third-party, unconfirmed) anecdotes are already hedged in-text, but journal
  reviewers may object to citing them at all. Keep the two CVEs (Cursor
  CVE-2025-54135, MCP filesystem CVE-2025-53109) as primary evidence; compress the
  anecdotes to one sentence with the hedge, or footnote them.
- **Fang et al. "87% of CVEs"** is methodologically contested (targets came with
  advisories; replication critiques exist). It is load-bearing twice ("LLM agents
  can exploit container CVEs autonomously"). Cite once, with a hedge.
- **Verified-kernel vs. evaluated-prototype gap**: the formal verification targets
  Inferno's kernel; the AgentDojo run is a Python filter; the 31-attack run is a Go
  9P server. Three loosely-coupled artifacts. The InferNode deployment (below) is
  the cheapest way to close this narratively.
- **GPT-5 temperature footnote appears three times** (Table 7 caption, §6.1.7 text,
  Table A.3 caption). Once is enough.

---

## 3. Suggested revision: one paragraph on the InferNode validation

Since submission of the preprint, the architecture has been validated end-to-end in
InferNode (production Inferno derivative; Veltro agents run with per-agent
namespaces over real 9P mounts). This directly addresses two standing weaknesses:
the "prototype only / small ecosystem" limitation and the future-work item
"end-to-end 9P integration." Recommended treatment — deliberately modest, no
product pitch:

> *Subsequent to the evaluation reported here, the architecture has been deployed
> end-to-end in a production Inferno derivative, in which each agent process
> receives a per-task namespace composed of 9P mounts and all tool interaction
> occurs through kernel-mediated file operations. This deployment exercises the
> verified `pgrpcpy()`/`namec()` code paths in Section 6.6 under real agent
> workloads, closing the gap between the verified kernel and the evaluated
> prototype.*

Place it in §7 (Discussion), either under Limitations (as a partial answer to the
ecosystem point) or as a short "Deployment experience" subsection, and delete the
corresponding future-work bullet. One paragraph, no new claims requiring new
experiments. Do **not** restructure the evaluation around it — that is the
ad-nauseam revision spiral you rightly want to avoid.

---

## 4. Trimming plan (~6–8 pages recoverable)

The "behavioral vs. structural" thesis is stated, by my count, in ten places; the
"Claude refused all 93, so hardening was never exercised" finding appears verbatim
four times; the container-orthogonality argument three times. Concrete cuts:

| # | Cut/merge | Est. saving |
|---|-----------|-------------|
| 1 | **Abstract**: halve. Drop CI bounds, state counts, tool-by-tool verification stats. One sentence per contribution; numbers limited to 0% cross-tool / 0.6% overall / 83.5% / "three verification tools, 0 violations". | ¼ p. |
| 2 | **Contributions list**: 6 → 4 (merge #1+#2 as the empirical claim; #3 stands; merge #4 semantic/syntactic into #3 or discussion; #5 efficiency; #6 is not a contribution, it's an artifact statement — fold into a footnote). | ¼ p. |
| 3 | **§2.3 Real-world incidents + §3.6 Threat landscape + §6.2.1 Isolation fallacy + related-work sandboxing**: four passes over "container boundary ≠ tool boundary." Keep §6.2.1 as the canonical treatment; reduce §2.3 to one paragraph + citations; delete §3.6 (its one novel point, the Fang citation, moves to 6.2.1); trim the related-work paragraph to two sentences. | 2 pp. |
| 4 | **§6.1.6 Hardened MCP + §6.1.9 Ablation + §6.2.2 Jailbreak scenario**: all three re-derive the same finding. Keep the ablation (it is the most structured), fold the hardened-MCP table into it, reduce the jailbreak scenario to its bullet list inside §6.2. | 1.5 pp. |
| 5 | **Two near-duplicate TCB tables** (`tab:tcb` in §3, `tab:tcb-verification` in §6.6) and **two verification summary boxes**. Keep one table (in §6.6) and one box; §3 gets a forward reference. | ¾ p. |
| 6 | **Theorem 1 box + "Formal basis" enumeration** repeat each other point-for-point. Keep the box (renamed), delete the enumeration, keep only the empirical-validation sentence. | ½ p. |
| 7 | **Conclusion**: the 5-bullet list restates the abstract verbatim. Replace with two paragraphs of prose; merge "Broader Implications" and "Call to Action" into one closing paragraph (journal registers poorly with manifesto endings). | ¾ p. |
| 8 | **Worked examples** (§7.3) duplicate §3.4 non-goals; keep the worked examples (they are concrete and good), cut the corresponding §3.4 bullets to one line each with a forward ref. | ¼ p. |
| 9 | **Related work**: Fuchsia, Spritely, E/EROS/Agoric lineage can compress to one paragraph — they establish pedigree, not baselines. The space freed pays for the CaMeL/tool-filter additions (M4/M5). | ½ p. |

Net effect: sharper paper at ~22–24 pp., with room for the new utility numbers
(M1) and the CaMeL comparison (M5) at no length increase.

---

## 5. Journal recommendations

This is a systems-security paper with formal methods and an AI-security hook. Field
context: nearly all peer work cited (AgentDojo, Progent, CaMeL) is conference-track;
security journals run 6–18 months, so the arXiv preprint carries currency while a
journal supplies the archival stamp. Ranked:

1. **ACM Transactions on Privacy and Security (TOPS)** — *best fit*. Publishes
   exactly this blend (OS-level enforcement mechanisms, empirical attack
   evaluation, formal verification). Capability-security lineage (Capsicum,
   ocaps) is home turf for its reviewer pool. Realistic first-decision ~4–6 months.
2. **IEEE Transactions on Dependable and Secure Computing (TDSC)** — highest
   impact factor of the plausible set; the TLA+/SPIN/CBMC verification story fits
   the "dependable" mandate well. Longer queue (often 9–15 months to acceptance)
   and heavier revision cycles. Choose this if maximizing venue prestige beats
   time-to-print.
3. **Computers & Security (Elsevier, COSE)** — pragmatic option: strong applied
   security journal, receptive to LLM/agent security papers *now*, fastest
   turnaround of the three (~3–6 months). Less prestigious than TOPS/TDSC but a
   reliable home.
4. **ACM DTRAP (Digital Threats: Research and Practice)** — backup; values
   real-world incident grounding and practitioner relevance, which this paper has
   in abundance. Lower tier.

Poor fits to skip: IEEE TIFS (forensics/signal-processing bent), JCS (slow, low
visibility), AI journals like TIST (reviewers won't value the OS/verification
depth, and will hammer the evaluation instead).

**Recommendation: TOPS.** It is the best venue whose reviewer pool will *reward*
the Plan 9/capability framing rather than treat it as exotica, and it is
prestigious enough to be "the best journal that might publish it." Submit to TDSC
instead only if impact factor is the deciding criterion and the timeline is
acceptable. If TOPS rejects with signal, COSE is the fast second shot.

**Sequencing**: fix M1–M2 (data integrity) and M5 (CaMeL) before *any* submission —
these are desk-reject/round-one-kill risks. M3–M4, M6–M7 and the trim can be done
in the same pass. The InferNode paragraph is a 30-minute edit. Everything in §2
(should-fix) is optional polish if time-boxed.
