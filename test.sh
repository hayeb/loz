#!/usr/bin/env bash

rm target/*.exe || true
rm target/*.ll || true

cargo build --release

while IFS= read -r -d '' file
do
  echo "Testing file $file"
  ./target/release/cloz $file || exit 1
  echo "Exit code: $?"
  filename="$(basename -s .loz $file)"
  output=$(./target/$filename)
  desired_output=$(cat "${file}.res")
  echo "Checking output.."
  if [ "$output" = "$desired_output" ]; then
    echo "OK"
  else
    echo "Output fail"
    echo "Got: $output"
    echo "Expected: $desired_output"
    exit 1
  fi
done <   <(find core/compiler/tests/programs/generator -name '*.loz' -print0)

echo "All tests passed"
