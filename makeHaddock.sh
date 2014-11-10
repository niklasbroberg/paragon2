#!/bin/bash
haddock -o HaddockDoc -h --ignore-all-exports \
  src/Language/Java/Paragon.hs \
  src/Language/Java/Paragon/Interaction.hs \
# Haddock doesn't understand these monads?
#  src/Language/Java/Paragon/Monad/Base.hs
