<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# `docs/wiki/` — in-repository source for the GitHub wiki

This directory is the **version-controlled source of truth** for the project
wiki. The GitHub wiki (<https://github.com/hyperpolymath/valence-shell/wiki>)
lives in a *separate* git repository (`valence-shell.wiki.git`) that is not
covered by pull-request review, CI, or the contractile invariants. Keeping the
canonical copy here means the wiki is reviewed, versioned, and diffable like any
other code.

## Audience-segmented structure

The wiki is organised as an **audience router**: a landing page sends each reader
to the track written for them. This satisfies the project requirement for
documentation tailored to five distinct audiences.

| Page | Audience |
|------|----------|
| `Home.md` | Landing page + audience router |
| `For-Lay-People.md` | Non-technical readers (no jargon) |
| `For-Users.md` | People installing and using the shell |
| `For-Developers.md` | Contributors, proof readers, builders |
| `For-Platform-Maintainers.md` | Packagers and deployers |
| `For-Marketers-and-Journalists.md` | Press & accuracy kit |
| `Verification-Status.md` | Shared honest-status reference |
| `_Sidebar.md` | Navigation shown on every wiki page |

## File-naming convention

These files use **GitHub wiki conventions** so they can be published to the wiki
verbatim:

- Page files are named with hyphens; GitHub renders `For-Lay-People.md` as the
  page **"For Lay People"**, reachable at `/wiki/For-Lay-People`.
- Inter-page links use the bare page name, e.g. `[For Users](For-Users)`.
- `Home.md` is the wiki landing page; `_Sidebar.md` is special (rendered on every
  page). Links to files *inside the main repo* (not wiki pages) use full
  `https://github.com/.../blob/main/...` URLs so they resolve from the wiki too.

## Publishing to the GitHub wiki

The wiki repo must be initialised once (create the first page via the GitHub UI),
after which:

```bash
# One-time: clone the wiki repo alongside the main checkout
git clone https://github.com/hyperpolymath/valence-shell.wiki.git

# Sync: copy the tracked source into the wiki working tree and push
cp docs/wiki/*.md ../valence-shell.wiki/
cd ../valence-shell.wiki
git add -A && git commit -m "sync wiki from docs/wiki/" && git push
```

(Automating this via a CI job on push to `main` is a reasonable future step; it
is intentionally left manual for now so wiki changes remain a deliberate act.)

## Editing rules

- **Honesty first.** Every page must stay consistent with
  `Verification-Status.md`, `docs/PROOF_HOLES_AUDIT.md`, and the repository's
  self-assessed status (v0.9.0, research prototype, not production-ready). If you
  update the status anywhere, update it everywhere — grep for the version string.
- Prose is licensed **CC-BY-SA-4.0** (SPDX header on every file).
- Don't duplicate canonical content; **link** to the source-of-truth files
  (`FAQ.adoc`, `QUICKSTART-*.adoc`, `docs/USER_GUIDE.md`, etc.) instead.
