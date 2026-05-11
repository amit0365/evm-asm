# benchmark-history

Append-only record of weekly `lake build` benchmark runs from
`.github/workflows/benchmark.yml` (issue #949 slice 3).

One JSON object per line in `history.jsonl`:

- `commit`        : full SHA of the commit benchmarked
- `ref`           : the branch / ref that triggered the run
- `timestamp`     : ISO 8601 UTC timestamp of when the record was appended
- `trigger`       : GitHub event name (`schedule` or `workflow_dispatch`)
- `run_id`        : GitHub Actions run ID (link target)
- `wall_seconds`  : `lake build` wall-clock time, integer seconds
- `wall_raw`      : raw `Elapsed (wall clock) time` string from `/usr/bin/time -v`
- `peak_rss_kb`   : peak resident set size in kilobytes
- `runner_os`     : `uname -s` of the runner
- `runner_cores`  : `nproc` on the runner
