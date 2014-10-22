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
\usepackage{proof}

% %include polycode.fmt
% %include lhs2TeX.fmt

%\setmainfont{XITS}
%\setmathfont{XITS Math}

\long\def\red#1{\color{red} #1 \color{black}}

\newenvironment{TODO}{%
  \color{blue} \itshape \begin{itemize}
}{%
  \end{itemize}
}


\title{Victor's Thesis Template}
\author{Victor}

\begin{document}
\maketitle
\tableofcontents

\theoremstyle{plain}
\newtheorem{thm}{Theorem}[chapter]
\newtheorem{crl}{Corolary}[chapter]
\newtheorem{prob}{Problem}[chapter]
\newtheorem{prop}{Proposition}[chapter]

\theoremstyle{definition}
\newtheorem{lemma}{Lemma}[chapter]
\newtheorem{mydef}{Definition}[chapter]
\newtheorem{notation}{Notation}[chapter]

\theoremstyle{remark}
\newtheorem{nota}{Note}[chapter]

\chapter{Prelude}
\label{chap:prelude}

  \section{Introduction}
  \label{sec:prelude:introduction}

  \section{The Problem}
  \label{sec:prelude:theproblem}
  
  \section{The Agda language}
  \label{sec:prelude:agdalanguage}
  \input{Agda_prelude.lagda}
  
\chapter{Background}
\label{chap:background}
\input{Background_prelude.lagda}

  \section{Notes on $\lambda$-calculus and Types}
  \label{sec:background:lambdacalculus}
  \input{Background_LambdaCalc.lagda}
  
\chapter{Martin-Löf's Type Theory}
\label{chap:martinlof}
  \input{MartinLof_prelude.lagda}

  \section{Introduction}
  \label{sec:martinlof:introduction}


\bibliographystyle{alpha}
\bibliography{../thesisbib}

\end{document}
