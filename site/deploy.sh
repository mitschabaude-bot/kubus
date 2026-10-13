#!/usr/bin/env bash
# Builds the website from origin/main and switches the served directory to it atomically.
#
#   site/deploy.sh [--force]
#
# A dedicated checkout ($KUBUS_SITE_SRC, default ~/sites/kubus-src) is updated to origin/main;
# if main's HEAD has not changed since the last deployment, nothing happens (unless --force).
# Otherwise kubus and the site are built into $KUBUS_SITE_DEST/builds/<sha>, and the symlink
# $KUBUS_SITE_DEST/current (served by nginx) is switched to it with a rename. The last three
# builds are kept.
# (the body is a function, so that the script is read completely before the checkout it
# lives in is updated)
main() {
  set -euo pipefail
  SRC=${KUBUS_SITE_SRC:-$HOME/sites/kubus-src}
  DEST=${KUBUS_SITE_DEST:-$HOME/sites/kubus}
  REPO=${KUBUS_SITE_REPO:-https://github.com/mitschabaude-bot/kubus.git}
  export PATH="$HOME/.elan/bin:$PATH"

  mkdir -p "$DEST/builds"
  exec 9>"$DEST/.lock"
  flock -n 9 || { echo "another deployment is running"; exit 0; }

  [ -d "$SRC/.git" ] || git clone -q "$REPO" "$SRC"
  git -C "$SRC" fetch -q origin main
  sha=$(git -C "$SRC" rev-parse origin/main)
  if [ "${1:-}" != --force ] && [ "$(cat "$DEST/deployed" 2>/dev/null)" = "$sha" ]; then
    exit 0
  fi
  echo "deploying $sha"
  git -C "$SRC" checkout -q --force --detach "$sha"
  (cd "$SRC" && lake build kubus)

  out="$DEST/builds/$sha"
  rm -rf "$out.tmp"
  KUBUS="$SRC/.lake/build/bin/kubus" python3 "$SRC/site/build.py" --out "$out.tmp"
  rm -rf "$out"
  mv "$out.tmp" "$out"
  ln -sfn "builds/$sha" "$DEST/current.new"
  mv -T "$DEST/current.new" "$DEST/current"
  echo "$sha" > "$DEST/deployed"
  ls -1dt "$DEST"/builds/*/ | tail -n +4 | xargs -r rm -rf
  echo "deployed $sha"
}
main "$@"; exit
