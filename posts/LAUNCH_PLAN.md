# Launch plan — boundary-axiom

**Status:** battle-ready locally; **not posted**. External launch begins only after
GitHub push and Pages are green.

**Global name:** `boundary-axiom`. No `boundary-report-core`; no third repo.

---

## 0 · Preflight (must all pass)

- [ ] `git push origin main` and `git push origin v1.0.1-site` succeeded.
- [ ] Pages source = **GitHub Actions**; `pages` workflow green.
- [ ] `https://limisys.github.io/boundary-axiom/` returns 200.
- [ ] `/technical.html` returns 200 and MathJax renders (3 display containers).
- [ ] `/evidence.html` and `/open-bridge.html` return 200.
- [ ] `site/assets/og.png` is reachable and 1200×630.
- [ ] Repo is public; README shows the public-pages block and the scope table.
- [ ] `posts/` contains no real name, email, employer, or local path.
- [ ] Archive hash `df1683f2…` is recorded in the Release notes; **not** described
      as on-chain, OTS-timestamped, or DOI-registered.
- [ ] The launch text still says: bridge open, level not unique, A7 model-class,
      gate not production, not a theory of consciousness.

If any item fails, do not post. A broken link or an overclaim on launch day costs
more than a delayed launch.

---

## 1 · Canonical links

Use these everywhere; no URL shorteners.

| Purpose | URL |
|---|---|
| Entry | `https://limisys.github.io/boundary-axiom/` |
| Technical edition | `https://limisys.github.io/boundary-axiom/technical.html` |
| Evidence | `https://limisys.github.io/boundary-axiom/evidence.html` |
| Open bridge | `https://limisys.github.io/boundary-axiom/open-bridge.html` |
| Repository | `https://github.com/limisys/boundary-axiom` |
| Full Lean source | `https://github.com/limisys/boundary-axiom/tree/main/lean` |
| Report core | `https://github.com/limisys/boundary-axiom/tree/main/report-core` |
| Gate | `https://github.com/limisys/boundary-axiom/blob/main/architecture/gate_reference.py` |

---

## 2 · Platform cards

### Hacker News — Show HN

- **URL field:** entry page.
- **Title:** `Show HN: The Boundary Is the Report – a Lean 4 core for boundary–report identity`
- **Text:** `posts/show_hn.md` (plain-text body).
- **Account:** normal HN account; no personal bio needed.
- **Risk:** HN will punish hype. Keep the “what is not claimed” paragraph.
- **Expected first question:** “Isn’t this just the standard Moore/closure
  correspondence?” Answer: yes, the math is standard; the contribution is the
  operationalization, the negative control, and the gate.

### LessWrong

- **Title:** `The boundary is the report: a conditional identity, and the counterexample that keeps it honest`
- **Body:** `posts/lesswrong.md`.
- **Tags:** `Alignment`, `Formal Methods`, `Agent Foundations`, `Lean` (use the
  closest existing tags; do not invent tags).
- **Link:** entry page in the first paragraph; technical edition at the end.
- **Account:** normal LW account.
- **Risk:** philosophical overread. Keep the “not a theory of consciousness”
  paragraph near the top.

### Alignment Forum

- **Title:** `Boundary–report identity on Moore families: a conditional result, a counterexample, and an open attribution bridge`
- **Body:** `posts/alignment_forum.md`.
- **Canonical:** if crossposting from LW, set the canonical URL to the LW post and
  note “crosspost”; otherwise use the entry page.
- **Tags:** `Alignment`, `Formal Methods`, `Agent Foundations`.
- **Account:** AF membership may be required. If posting is unavailable, use the
  LW post and link it from the AF-relevant discussion; do not create a duplicate
  without the canonical note.
- **Risk:** AF readers will ask for the alignment payoff. Lead with the
  report-as-constraint framing, not the self-awareness premise.

### X — AI Alignment

- **Thread:** `posts/x_ai_alignment.md`.
- **Media:** `site/assets/og.png`.
- **Tags:** `#AIAlignment #AgentFoundations #Lean4`.
- **Link:** tweet 8 (entry + technical + repo).

### X — Functional Programming

- **Thread:** `posts/x_functional_programming.md`.
- **Media:** `site/assets/og.png`.
- **Tags:** `#FunctionalProgramming #CategoryTheory #FormalMethods #Lean4`.
- **Link:** tweet 7.

### X — Lean 4

- **Thread:** `posts/x_lean4.md`.
- **Media:** `site/assets/og.png`.
- **Tags:** `#Lean4 #Mathlib #FormalVerification`.
- **Link:** tweet 7.
- **Ask:** proof review of the v1.1 Moore statements and the `UpClosed` audit.

---

## 3 · Timing

All times relative to the moment Pages is green.

| T | Action | Why |
|---|---|---|
| T−30m | Preflight; open all links in a logged-out browser; capture screenshots | catch broken Pages/cache |
| T+0 | HN Show HN | HN traffic is front-loaded; be present to reply |
| T+10m | LessWrong longform | gives a substantive link for HN commenters |
| T+20m | Alignment Forum (or canonical crosspost note) | AF audience separate from HN |
| T+30m | X AI Alignment thread | cross-link HN/LW |
| T+45m | X FP thread | different audience; do not quote-retweet the first thread immediately |
| T+60m | X Lean 4 thread | proof-review audience |
| T+0–2h | Reply window | first wave decides the frame; use `posts/reply_bank.md` |
| T+2–6h | Collect critiques; no edits to the formal claim without a commit | preserve a stable artifact |
| T+24h | Post a short “what changed / what was challenged” note if substantive | shows good faith |

Do not post all X threads in the same minute; it reads as bot behavior. Do not
crosspost the HN link into every reply.

---

## 4 · Reply discipline

1. **Concede the standard parts.** The Moore/closure correspondence is standard.
   Say so before pointing to the contribution.
2. **Do not improvise a stronger claim.** If asked about attribution, link
   `open-bridge.html`; do not say “almost done.”
3. **Separate scopes.** 56/467/90 full corpus; 6/45/13 report core; 1/33/7 A
   module. Never add them.
4. **Accept the toy-gate critique.** The gate is a finite-state reference; the
   production question is open.
5. **Correct errors publicly.** If a count or link is wrong, fix the repo, then
   reply with the correction. Do not silently edit the post.
6. **No priority claims.** “Independent release” is fine; “first” is not.

Prepared answers: `posts/reply_bank.md`.

---

## 5 · Success criteria

Not upvotes. Success is:

- at least one **non-trivial technical objection** that can become a commit or a
  debt entry;
- at least one **independent reproduction attempt** (build, gate run, or
  counterexample check);
- no successful catch of an overclaim, broken link, or count error;
- a clear record of what was challenged and what changed.

A quiet launch with one good critique is better than a loud launch with a
tautology.

---

## 6 · Abort / rollback

- **Pages down:** link the GitHub repo; do not link a dead Pages URL.
- **Wrong count or claim:** edit the repo/site, push a fix, then reply with the
  corrected link. Do not argue.
- **Hostile thread:** answer the strongest technical point once; do not feed a
  pile-on.
- **No AF access:** keep the AF draft unpublished; use LW as canonical and link it
  where appropriate.
- **No HN traction:** do not repost immediately; wait at least a day and only with
  a materially different angle.

---

## 7 · Artifact map

```
posts/show_hn.md                  HN body
posts/lesswrong.md                LW longform
posts/alignment_forum.md          AF longform
posts/x_ai_alignment.md           X AI alignment thread
posts/x_functional_programming.md X FP thread
posts/x_lean4.md                  X Lean thread
posts/x_thread.md                 generic/archive thread
site/assets/og.png                social card
docs/OPEN_BRIDGE.md               public bridge statement
```

The launch is a **research release**, not a product launch. The artifact is the
claim and its limits.
