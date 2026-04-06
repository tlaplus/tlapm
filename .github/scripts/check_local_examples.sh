#!/usr/bin/env bash

set -u
set -o pipefail

usage() {
  echo "Usage: $0 [path-to-tlapm]" >&2
}

if [ "$#" -gt 1 ]; then
  usage
  exit 1
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
cd "$repo_root"
tlapm=${1:-./_build/tlapm/bin/tlapm}

case "$tlapm" in
  /*) ;;
  *) tlapm="$repo_root/${tlapm#./}" ;;
esac

if [ ! -x "$tlapm" ]; then
  echo "TLAPM binary is not executable: $tlapm" >&2
  exit 1
fi

skip_example() {
  case "$1" in
    examples/paxos/Paxos.tla|examples/ByzPaxos/BPConProof.tla|examples/GraphTheorem.tla)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

checked_count=0
skipped_count=0
total_count=0
failed_examples=()

while IFS= read -r file; do
  [ -n "$file" ] || continue
  total_count=$((total_count + 1))

  if skip_example "$file"; then
    skipped_count=$((skipped_count + 1))
    printf 'Skipping %s\n' "$file"
    continue
  fi

  checked_count=$((checked_count + 1))
  printf 'Checking %s\n' "$file"

  dir=$(dirname "$file")
  base=$(basename "$file")
  if ! (
    cd "$repo_root/$dir" &&
    "$tlapm" --cleanfp --stretch 5 "$base"
  ); then
    failed_examples+=("$file")
    printf 'Failed %s\n' "$file"
  fi
done < <(find examples -type f -name '*.tla' | LC_ALL=C sort)

if [ "$total_count" -eq 0 ]; then
  echo "No local examples were found under examples/." >&2
  exit 1
fi

printf '\nLocal examples summary: total=%d checked=%d skipped=%d failed=%d\n' \
  "$total_count" "$checked_count" "$skipped_count" "${#failed_examples[@]}"

if [ "${#failed_examples[@]}" -gt 0 ]; then
  printf 'Failed example proofs:\n'
  for file in "${failed_examples[@]}"; do
    printf '  %s\n' "$file"
  done
  exit 1
fi
