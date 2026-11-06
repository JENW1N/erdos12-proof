#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
mkdir -p .verification-output
lake env lean -j 2 -M 8192 -o .lake/build/lib/lean/Challenge.olean Challenge.lean
lake env leanexport Challenge -- Quot Quot.mk Quot.lift Quot.ind PrizeTarget.all_parts propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam > .verification-output/challenge.ndjson
lake env leanexport Submission -- Quot Quot.mk Quot.lift Quot.ind PrizeTarget.all_parts propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam > .verification-output/solution.ndjson
lake comparator --config comparator.json --challenge-from-export .verification-output/challenge.ndjson --solution-from-export .verification-output/solution.ndjson --inadvisably-no-sandbox
