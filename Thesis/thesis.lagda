\documentclass{report}
\usepackage[english]{babel}
\usepackage[utf8x]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{graphicx}

\usepackage{url}
\usepackage{alltt}
\usepackage{listings}
\usepackage{fancyvrb}
\usepackage{float}
\usepackage[usenames,dvipsnames]{color}
\usepackage{enumerate}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{makeidx}
\usepackage{parskip}
\usepackage{multirow}
\usepackage{moreverb}
\usepackage{agda} 

%include lhs2TeX.fmt

\title{Victor's Thesis Template}
\author{Victor}

\begin{document}
\maketitle
\tableofcontents

Document template.

\begin{code}
data Bool : Set where
  true false : Bool
\end{code}

And some natural numbers:
\include{chap01.lagda}

\end{document}
