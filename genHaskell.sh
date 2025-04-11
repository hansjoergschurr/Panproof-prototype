#!/usr/bin/env bash

echo "Terms"
agda2hs ./src/agda/Core/Terms.agda -o ./src/haskell/
echo "Proofs"
agda2hs ./src/agda/Core/Proofs.agda -o ./src/haskell/