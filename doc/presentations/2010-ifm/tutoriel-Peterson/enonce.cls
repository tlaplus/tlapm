% vim: syntax=tex

% Classe de documents pour sujets et corrections de TD/TP.
%
% Forme générale:
%
%   \documentclass{enonce}
%   \course{titre du cours}     % optionnel
%   \title{titre de l'énoncé}
%   \date{comme d'hab}
%   \begin{document}
%   \maketitle
%     ...
%   \end{document}
%
% Format des exercices:
%
%   \begin{exercice}[texte optionnel]{un titre éventuellement vide}
%     ...
%     \begin{questions}
%     \item Première question...
%     \item Deuxième question
%     \end{questions}
%     ...
%   \end{exercice}
%
% Le texte optionnel permet de dire par exemple \begin{exercice}[TP]{Blop}
% pour ajouter un commentaire sur le type d'exercice. Avec l'environnement
% "exercice*", le texte commence sur la même ligne que le titre.
%
%   \begin{correction}
%     ...
%   \end{correction}
%
% L'option de classe "correction" sert à activer l'impression des corrections,
% sans cette option les environnements "correction" sont ignorés.
%
% Les environnements "question" peuvent être imbriqués pour faire des
% sous-questions (à profondeur 2 actuellement mais ajouter des niveaux
% consiste simplement à définir des compteurs questiiion, questivon, questvon,
% questvion, etc).

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{enonce}[2006/02/15 sujets de TD/TP]

% On se base sur la classe article pour avoir les sections, etc.

\LoadClass[a4paper,10pt]{article}

\DeclareOption{correction}{\@correctiontrue}
\newif\if@correction
\@correctionfalse
\ProcessOptions

% Réglages pour le français

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\SetUnicodeOption{mathletters}
\RequirePackage[T1]{fontenc}
\RequirePackage[frenchb,english]{babel}
\RequirePackage{graphicx,alltt,hyperref}
%\FrenchItemizeSpacingfalse


% Mise en page

\RequirePackage[a4paper,width=15cm,height=22cm]{geometry}

\RequirePackage{charter,euler}

% Format du titre

\RequirePackage{ifthen}

\def\course#1{\gdef\@course{#1}}
\def\@course{}

\def\@maketitle{%
  \newpage
  \null
  \vskip 2em%
  \begin{center}%
  \let \footnote \thanks
    \ifthenelse{\equal{\@course}{}}{}{%
      {\Large \@course \par}%
      \vskip 1em}%
    {\LARGE \@title \par}%
    \vskip 1em%
    {\large \@date \par}%
  \end{center}%
  \par
  \vskip 1.5em}

% Sections

\RequirePackage[medium]{titlesec}



% Quelques packages utiles

\RequirePackage{url,moreverb,listings}
\RequirePackage{amssymb,amsmath,stmaryrd}
\RequirePackage{array}

% Verbatim amélioré

\RequirePackage{moreverb}
\renewcommand\verbatimtabsize{4\relax}

% Listings

\RequirePackage{listings}
\lstset{
  columns=flexible,
  numbers=none,
  xleftmargin=\parindent,
  basicstyle=\ttfamily,
  showstringspaces=false
}



% Quelques macros utilitaires

\def\code{\lstinline[basicstyle=\ttfamily]}

\newcommand\cmd[1]{«~\texttt{#1}~»}
\newcommand\cmdarg[1]{\rmfamily{\emph{#1}}}

\def\NN{\mathbb{N}}
\let\leq\leqslant
\let\geq\geqslant
\let\epsilon\varepsilon
