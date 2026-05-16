# hawk-m4-asm download bundle

Snapshot of the work done on the `hawk-m4-asm` branch of
`amit0365/pqm4`. The branch was never pushed (sandbox had no
GitHub credentials).

## Contents

```
hawk-m4-handoff/
├── README.md                  # this file
├── hawk512/                   # crypto_sign/hawk512/ from the fork
│   └── m4/                    #   ← all the new HAWK-512 source
│       ├── HANDOFF.md         #   START HERE — full project-transfer doc
│       ├── PLANTARD_NOTES.md  #   technical log of the NTT investigation
│       ├── NOTES.md           #   older / narrower SHAKE-swap notes
│       ├── api.{c,h}, hawk_*.{c,h}, modq.h, ng_*.{c,h}, sha3.{c,h}
│       ├── plant_18433.{c,h}  #   Plantard path scaffolding (Path B form)
│       └── tests/             #   host-only cross-check tests
├── hawk1024/                  # crypto_sign/hawk1024/ from the fork
│   └── m4/                    #   mostly symlinks to ../../hawk512/m4/
│                              #   (api.h, api.c, LICENSE.txt are per-variant)
└── patches/                   # 12 git format-patches, master..hawk-m4-asm
    ├── 0001-Add-HAWK-512-and-HAWK-1024-m4-scheme-scaffolds.patch
    ├── 0002-Vendor-HAWK-reference-C-as-pqm4-m4-baseline.patch
    ├── 0003-SHAKE-256-route-HAWK-s-sha3-API-to-pqm4-s-Keccak-asm.patch
    ├── 0004-Add-host-cross-check-tests-for-the-SHAKE-SHA3-glue.patch
    ├── 0005-Plantard-NTT-design-note-and-calibration-test-scaffo.patch
    ├── 0006-Plantard-NTT-lock-the-encoding-via-calibration.patch
    ├── 0007-Plantard-NTT-portable-C-plant-path-cross-check-HAWK_.patch
    ├── 0008-Plantard-NTT-experiment-a-follow-up-ml-dsa-s-wrap-ar.patch
    ├── 0009-Plantard-NTT-record-the-Path-A-dead-end-and-reset-to.patch
    ├── 0010-Plantard-NTT-experiment-a-result-ml-dsa-uses-pipelin.patch
    ├── 0011-Plantard-NTT-experiment-a-follow-up-ml-dsa-s-wrap-ar.patch
    └── 0012-Add-HANDOFF.md-for-next-agent-transfer.patch
```

## How to use this bundle

### Option 1: just drop the new dirs into a pqm4 fork

If you already have a pqm4 clone:

```
cd /path/to/your/pqm4
cp -r /path/to/hawk-m4-handoff/hawk512  crypto_sign/
cp -r /path/to/hawk-m4-handoff/hawk1024 crypto_sign/
git add crypto_sign/hawk512 crypto_sign/hawk1024
git commit -m "Add HAWK-m4 scheme (squashed)"
```

You lose the commit history but get the final state in one shot.

### Option 2: replay the full commit history (recommended)

```
cd /path/to/your/pqm4
git checkout -b hawk-m4-asm
git am /path/to/hawk-m4-handoff/patches/00*.patch
```

This recreates the exact 12-commit branch as it was on the
sandbox. **Recommended** — the commit messages document why
each step happened.

### Option 3: push the branch from a machine with GitHub auth

If you have the original repo checked out (the one used in the
sandbox), just `git push -u origin hawk-m4-asm`. The branch is
ready to go; the only reason it wasn't pushed is the sandbox
had no GitHub credentials.

## First file to read

`hawk512/m4/HANDOFF.md` — the next-agent transfer document.

It covers: project goal, repo state, what's done, what's pending,
test commands, the Plantard NTT saga, specific pitfalls, the
recommended Path B next step (write `plant_18433_cm4.S`), and
the verification cycle.

## Spec adherence note

Commits in this bundle are **unsigned**. The sandbox's commit-
signing service is scoped to one specific repo and rejected
signatures for this work. If your project requires signed
commits, re-apply with `git am -S` (after configuring a signing
key locally).
