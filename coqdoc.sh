#!/bin/bash

coqdoc Stlc.v --latex \
    --no-index \
    -d ./doc \
    --title 'Formally Proving Validity for Type-Based Information Flow' \
    -toc \
    --preamble '\usepackage{bussproofs} \usepackage{amssymb} \usepackage{latexsym} \def\fCenter{{\mbox{\Large$\rightarrow$}}}' \
    -g # hide proofs by default
