#!/bin/bash

# coqc -Q . STLCIF Maps.v Smallstep.v Stlc.v

coqdoc Stlc.v --latex \
    --no-index \
    -d ./doc \
    --title 'Formally Proving Validity for Type-Based Information Flow' \
    --table-of-contents \
    --preamble '\usepackage{bussproofs} \usepackage{amssymb} \usepackage{latexsym} \def\fCenter{{\mbox{\Large$\rightarrow$}}} \usepackage{titlesec} \usepackage{lipsum} \usepackage{setspace}' \
    -g # hide proofs by default

# \tableofcontents

# \titleformat{\chapter}[display]
#   {\normalfont\bfseries}{}{0pt}{\Huge}
# 
# \begin{titlepage}
# \begin{center}
# 
# \begin{spacing}{1.5}
#     \vspace*{\fill}
# \end{spacing}
# 
# \begin{spacing}{2.5}
#     \textbf{\Large A Machine-verified Proof for Information Flow Typing}\\[0.5cm]
#     \vspace*{\fill}
# \end{spacing}
# 
# \begin{spacing}{1.15}
#     \textbf{\large Jacob Bennett}
#     \date{}
# \end{spacing}
# 
# \end{center}
# \end{titlepage}
