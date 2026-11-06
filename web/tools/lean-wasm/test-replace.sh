#!/usr/bin/env bash
set -euo pipefail
source_tree=$1
native_prefix=$2
output=$3
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$output"
"${LEAN_BROWSER_TEST_CXX:-c++}" -std=c++17 -O2 \
  -I"$source_tree/src" -I"$native_prefix/include" "$here/test-replace.cpp" \
  -L"$native_prefix/lib/lean" -L"$native_prefix/lib" \
  -Wl,-rpath,"$native_prefix/lib/lean",-rpath,"$native_prefix/lib" \
  -lleancpp -lleanshared -lc++ -o "$output/test-replace"
"$output/test-replace"
