#!/usr/bin/env bash

echo "Terms"
agda2hs ./src/agda/Core/Terms.agda -o ./src/haskell/

echo "Proofs"
agda2hs ./src/agda/Core/Proofs.agda -o ./src/haskell/

echo "Rules"
agda2hs ./src/agda/Core/Rules.agda -o ./src/haskell/