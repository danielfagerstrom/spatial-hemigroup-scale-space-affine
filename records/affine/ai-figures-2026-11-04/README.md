# AI figures for the affine paper, computed 2026-11-04

The archivist's re-derivation for pass 5 (article-kit `PROCESS.md` § 8), read-only over `ai-archive/canonical/`, after the
author teleported the cloud sessions and the archive's daily job ran (commit "chronicle: 2026-11-04"). `rec3.py` is its script, with one row
added by the session ("AI reports out, all terminal text kept"); `rec3-output.txt` is the session's own run of it the same day. The
exclusions are data in the script. It prints counts and timestamps only.

**One cut for everything: 2026-11-04 20:33:13 UTC**, the archive's last turn at the daily job of that evening, ahead of the freeze. The session that wrote this is counted to that cut.

## The figures

Lower bounds on the agents' words. Active time caps each gap at fifteen minutes and includes subagents' time, so it is not the author's hours.

| | Core | Ceiling |
|---|---|---|
| Sessions / subagent traces | 76 / 336 | 80 / 352 |
| First archived turn (UTC) | 2026-09-25 01:37 | 2026-09-21 16:31 |
| Last archived turn (UTC) | 2026-11-04 20:33 | 2026-11-04 20:33 |
| Archived days | 31 | 37 |
| Agents' words, subagents included | 226,726 | 346,885 |
| Typed, raw (`typed_words`) | 21,172 / 204 turns (10.7) | 30,338 / 453 turns (11.4) |
| Typed, AI reports out, **all terminal text kept** | 6,530 (**34.7**) | 15,696 (**22.1**) |
| Typed, AI reports and the one session's terminal text out (the archivist's headline) | 5,919 (38.3) | 15,085 (23.0) |
| Typed, AI reports, that terminal text and **every `<pasted_content>` block out** | 5,823 (**38.9**) | 13,214 (**26.3**) |
| Headline row without the Lean session | 5,536 against 197,899 (35.7) | 14,702 against 318,058 (21.6) |
| Active hours / summed spans | 173.8 / 732.6 | 241.1 / 1,146.9 |

**Quote 22 to 39 to 1.** Pasted text that is not an AI report is not obviously the author's: the archivist's headline took one session's terminal turns out and
left the others' in. So the range quoted is the widest that text can make it: 22.1 with only the AI reports out, and 38.9 with every pasted block out as well (96 words in the
core, 1,871 in the ceiling, which are not all shown to be terminal text). The 22.1 end still counts 611 words of terminal text as typed, and turns under 100 words were not classified.

## The scoping

- **Core**: every `claude-code` session whose `repo` starts `spatial-hemigroup-affine-` (51 queue runs, 14 evaluator runs, one review run); the hub's Paper
  VII session `7dbafaad` whole; the Lean session `dd33ba56` whole; every other `claude-code` session whose title or branch names "affine", other than
  the hub shift `a94448d1` (`63253a80`, `53a4f41c`, `a34cd72a`, `3c3842d5`, `0cad1fd5`, `25478c56`); and by id `057cfca0` and `33b1ecdc`.
- **Ceiling**: core plus the four hub shift sessions `89a0f801`, `46d612ec`, `47dc0065`, `a94448d1`.
- This widens `records/affine/ai-figures-2026-10-11/rec.py`, whose pattern misses the evaluator and review tags and the worktree and cloud sessions.
- Five other sessions the author teleported are hub sessions unrelated to this module (`f6913bdb` with one mention of "affine", the others none), and stay out.

The merged pull requests since 2026-10-18, #154 to #178, are all covered: #154–#159 and #164 by the queue runs, #160–#161 by `0cad1fd5`
(`claude/brave-allen-is86zu`), #162–#163 and #165–#169 by `25478c56` (`claude/serene-newton-jcolkg`), #170–#177 by `057cfca0`
(`claude/inspiring-euler-r9evdv`). #178 was this session's, `33b1ecdc`: the archivist found no mention of its branch in the canonical text and reported it uncovered,
which the session corrects from its own record. The link is by branch, date and title; the teleports' branch stamp is unreliable (`ai-archive/salvaged.json`).

## Text in the typed words that is not the author's

| Session | Timestamp (UTC) | Words out | What | Firmness |
|---|---|---|---|---|
| `7dbafaad` | 2026-10-12 07:44:22 | 5,454 | a referee report by GPT-6.1 Sol Ultra | firm |
| `7dbafaad` | 2026-10-12 07:45:24 | 2,145 | a second such report | firm |
| `057cfca0` | 2026-11-03 18:02:04 | 7,043 of 7,047 | a report headed Gemini 4 Argon High, the 4-word label kept | firm; which round is not read |
| `0cad1fd5` | 2026-10-24 08:49:11 | 161 | terminal session text | firm that it opens with a shell prompt; the rest not read |
| `0cad1fd5` | 2026-10-24 10:38:22 | 172 | as above | as above |
| `0cad1fd5` | 2026-10-24 13:39:34 | 278 | as above | as above |

Every typed turn of 100 words or more in the four added sessions was classified by its opening; the other two, in `25478c56` (224 and 225 words), are the author's prose. Turns under
100 words were not classified.

## What the figures do not hold

- **The subagents of two cloud sessions.** Teleport does not carry them: `057cfca0` has 25 Agent calls, `25478c56` five, and no trace of any (`0cad1fd5` made none). A kept trace carries few words of visible
  prose (about 50 on the sessions that have the most), so these are under 1% of the core's agents' words. **That says little of the work**: a trace's turns are many, 37 to 127 each, and they are mostly tool calls, which the words do not count.
- **The external reviewers' own text.** The five Fable 5.1 referees' words are in no count: no Fable turn appears in the added sessions. Gemini's and GPT's reports are out of both counts by the table above; only one Gemini report was pasted as such. The reports themselves are in `records/affine/reviews/`.
- Words count visible prose only, so code, LaTeX and proofs written through tool calls are not in the agents' count.
- Hub time spent on this module inside sessions named for something else is missed, and the Paper VII session is counted whole though it also managed other work.
- Work after the cut. `repos.json` has no entry for this repository, so commit attribution does not reach it; commit counts are `git log`'s.

## Since `iso-v0.1`, not quoted

From the tag (2026-10-14 05:27:52 UTC), slicing the hub and shift sessions by turn, the archivist's headline: core 1,754 typed words against 57,217, ratio 32.6, 29.1 h active, 15 days; ceiling 2,096 against
64,949, ratio 31.0, 35.1 h. Not the affine paper's alone: Q-0470 and Q-0474 to Q-0476 were for the isotropic paper's next version. So the statement does not divide the figures.

## The earlier derivations

- `records/affine/ai-figures-2026-10-13.md` stays the derivation for `iso-v0.1`, which quotes 22 to 42 over sixteen days.
- Earlier on 2026-11-04, before the teleports, this directory held `rec2.py`, which gave 22 to 40 to the cut of 2026-11-03 (in git). `rec3.py` first ran to 11:03 UTC that day and gave 22 to 39, as it does now.
