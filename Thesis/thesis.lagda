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

%include polycode.fmt
%include lhs2TeX.fmt

\title{Victor's Thesis Template}
\author{Victor}

\begin{document}
\maketitle
\tableofcontents

\chapter{Prelude}
\label{chap:prelude}

  \section{Introduction}
  \label{sec:introduction}

  \section{The Problem}
  \label{sec:theproblem}
  
  \section{Agda language}
  \label{sec:agdalanguage}
  \input{SectionAgdaLang.lagda}

\chapter{Background}
\label{chap:background}

\end{document}
