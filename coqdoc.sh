#!/bin/bash

coqdoc Stlc.v --latex \
    --no-index \
    -d ./doc \
    --title 'Formally Proving Validity for Type-Based Information Flow' \
    -toc \
    -g # hide proofs by default
