#!/usr/bin/env bash

set -e

rm target/*.exe || true
rm target/*.ll || true

cargo build --release

while IFS= read -r -d '' file
do
  echo "Testing file $file"
  ./target/debug/cloz $file || exit 1
  filename="$(basename -s .loz $file)"
  output=$(./target/$filename)
  desired_output=$(cat "${file}.res")
  if [ "$output" = "$desired_output" ]; then
    echo "OK"
  else
    echo "Output fail"
    echo "Got: $output"
    echo "Expected: $desired_output"
    exit 1
  fi
done <   <(find core/compiler/tests/programs -name '*.loz' -print0)