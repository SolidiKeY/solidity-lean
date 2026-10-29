#!/bin/bash
set -u
root=/workspace/solidity-lean
compiler=/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js
combined=0
for fixture in test/libsolidity/semanticTests/tryCatch/create.sol test/libsolidity/semanticTests/libraries/external_call_with_storage_mapping_parameter.sol test/libsolidity/semanticTests/functionCall/creation_function_call_with_args.sol; do
 case "$fixture" in
  */tryCatch/*) label=try-create ;;
  */libraries/*) label=library-mapping ;;
  *) label=dynamic-create ;;
 esac
 node scripts/solidity-upstream.mjs run --compiler "$compiler" --filter "$fixture" --batch-size 1 --out "tests/contract-world-certificates/upstream/$label"
 code=$?
 echo "fixture=$fixture exit=$code"
 if [ "$code" -ne 0 ]; then combined=1; fi
done
exit "$combined"
