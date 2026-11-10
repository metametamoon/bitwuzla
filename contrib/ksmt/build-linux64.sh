#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)
out=${1:-$(mktemp -d)}

docker build \
  --build-arg BASE_REGISTRY="${BASE_REGISTRY:-docker.io}" \
  --target out \
  --output "type=local,dest=$out" \
  -f "$root/contrib/ksmt/Dockerfile.linux64" \
  "$root"

cat "$out/libbitwuzla.so.sha256"
echo "$out"
