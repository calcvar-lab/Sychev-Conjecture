#!/usr/bin/env bash

# Update Mathlib and the Lean toolchain.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../lean"

# Keep the pinned Lake dependency on a tag matching the chosen Lean version.

tag=${1:?Usage: bash scripts/update.sh vX.Y.Z}
if [[ ! $tag =~ ^v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
    printf 'Expected a Mathlib release tag, such as v4.33.1.\n' >&2
    exit 2
fi
toolchain=$(curl --fail --silent --show-error --location "https://raw.githubusercontent.com/leanprover-community/mathlib4/$tag/lean-toolchain")
printf '%s\n' "$toolchain" > lean-toolchain
sed -i.bak "s/^rev = .*/rev = \"$tag\"/" lakefile.toml
rm -- lakefile.toml.bak
lake update
