#!/usr/bin/env bash
#
# Build + install the custom Agda 2.9 (from the Agda source checkout) and pin its
# nix-store runtime dependencies with GC roots so the binary keeps working
# across `nixos-rebuild` + garbage collection.
#
# Why this exists: `cabal install` on NixOS produces a binary that links the
# system glibc/gmp/etc. from the nix store. Those paths are NOT GC roots, so a
# later `nixos-rebuild` + `nix-collect-garbage` deletes them and the agda
# binary stops running ("no such file or directory" on its ELF interpreter).
# Re-run this script after you rebuild your system, or after patching Agda.
#
# Usage:  bash scripts/build-agda.sh [AGDA_SRC_DIR]
#   AGDA_SRC_DIR defaults to /home/n/agda
set -euo pipefail

AGDA_SRC="${1:-/home/n/agda}"
BINDIR="$HOME/.local/bin"
GCDIR="$HOME/.local/state/agda-gcroots"   # indirect GC roots live here
AGDA="$BINDIR/agda"

[ -d "$AGDA_SRC" ] || { echo "error: Agda source checkout not found: $AGDA_SRC" >&2; exit 1; }
mkdir -p "$BINDIR" "$GCDIR"

echo "==> Building Agda from $AGDA_SRC (ghc $(ghc --version 2>/dev/null | grep -o '[0-9.]*$'))"
( cd "$AGDA_SRC" && cabal install exe:agda \
    --overwrite-policy=always --install-method=copy --installdir="$BINDIR" )

echo "==> Verifying the binary runs"
"$AGDA" --version
# Confirm the ES6 JS backend (the reason agdelte needs 2.9) is present.
if "$AGDA" --help 2>&1 | grep -q -- '--js-es6'; then
  echo "    --js-es6 supported: OK"
else
  echo "    WARNING: --js-es6 not found in this agda's options" >&2
fi

echo "==> Pinning nix-store runtime deps as GC roots (so a system GC won't break it)"
if command -v nix-store >/dev/null 2>&1; then
  # Collect the store paths the binary depends on: ELF interpreter + shared libs.
  paths=""
  if command -v patchelf >/dev/null 2>&1; then
    paths="$(patchelf --print-interpreter "$AGDA" 2>/dev/null || true)"
  fi
  paths="$paths
$(ldd "$AGDA" 2>/dev/null | grep -o '/nix/store/[^ ]*' || true)"
  rooted=0
  while IFS= read -r p; do
    [ -z "$p" ] && continue
    # Reduce a /nix/store/HASH-name/... path to its top-level store path.
    top="$(printf '%s' "$p" | sed -E 's#(/nix/store/[^/]+).*#\1#')"
    [ -e "$top" ] || continue
    name="$(basename "$top")"
    if nix-store --realise "$top" --add-root "$GCDIR/$name" --indirect >/dev/null 2>&1; then
      rooted=$((rooted + 1))
    fi
  done < <(printf '%s\n' "$paths" | sort -u)
  echo "    pinned $rooted store path(s) under $GCDIR"
else
  echo "    nix-store not available — skipping GC-root pinning" >&2
fi

echo "==> Done. agda 2.9 installed at: $AGDA"
