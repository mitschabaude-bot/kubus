# The Kubus website

`site/build.py` builds the website into `site/_site` (or `--out DIR`): the landing page (`site/index.md`), the tutorial (`docs/tutorial/*.md`) and the library browser (`lib/*.ktt`). It needs Python 3 (standard library only) and a built `kubus` (`lake build kubus`; override the binary with `KUBUS=…`). Links are relative, so the output works under any base URL.

## Code blocks

Every ```` ```kubus ```` block of a chapter is elaborated by `kubus --doc` (see `Kubus/Doc.lean`): the blocks of one chapter form one module, in order, so later blocks see earlier definitions; imports are written in the blocks. The JSON from `kubus --doc` gives every token its class, the type of the identifier under it (shown on hover), the definition site of globals (links into the library pages), the output of `#eval`/`#check`, errors, goals of holes, and the kernel's verdict per declaration (✓ in the gutter).

- ```` ```kubus fails ```` — the block must raise an error, which is shown under the failing declaration.
- ```` ```kubus hole ```` — the block may contain `?` holes; their goals are shown.
- ```` ```kubus-lib MODULE NAME… ```` — shows the named declarations of `lib/MODULE.ktt`, rendered like the library pages.

The build fails if any other block raises an error, contains a hole, or contains a declaration that the kernel does not certify, if a `fails` block does not fail, or if a library declaration is not certified. `tests/run.sh` runs the build, and so does CI.

## Deployment

The site is served from this server: nginx serves `/var/www/kubus`, which points to `~/sites/kubus/current` (owned by the agent user). `site/deploy.sh` updates a dedicated checkout (`~/sites/kubus-src`) to `origin/main`, and if main's HEAD changed since the last deployment, builds kubus and the site into `~/sites/kubus/builds/<sha>` and switches the `current` symlink to it atomically (the last three builds are kept). `--force` rebuilds anyway.

A systemd user timer runs it every ten minutes:

```
cp site/systemd/kubus-site.{service,timer} ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now kubus-site.timer
systemctl --user list-timers kubus-site.timer      # next run
journalctl --user -u kubus-site.service            # logs
```

The service runs `~/sites/kubus-src/site/deploy.sh` (clone the repository there first, or run `site/deploy.sh` once from any checkout).
