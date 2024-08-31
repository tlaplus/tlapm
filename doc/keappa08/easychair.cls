%
% Some credits
%

\def\easychairstyleauthor{EasyChair Style, by Serguei A. Mokhov <mokhov@encs.concordia.ca> <01 June 2008>}
\def\easychairstylerevision{$Id: easychair.cls,v 1.17 2008/06/19 16:14:49 mokhov Exp $}
\def\easychairstylepurpose{Designed for EasyChair.org, under guidelines and suggestions of}
\def\easychairstylevoronkov{\space\space\space\space\space\space\space\space\space\space\space\space\space Andrei Voronkov <www.voronkov.com>, and}
\def\easychairstylesutcliffe{\space\space\space\space\space\space\space\space\space\space\space\space\space Geoff Sutcliffe <www.cs.miami.edu/^geoff>}
\def\easychairstylecopyright{Copyright terms are that of EasyChair.org}
\def\easychairstylebugs{For bug reports, please contact <mokhov@encs.concordia.ca>}

\everyjob{\typeout{\easychairstyleauthor}}
\everyjob{\typeout{\easychairstylerevision}}
\everyjob{\typeout{\easychairstylepurpose}}
\everyjob{\typeout{\easychairstylevoronkov}}
\everyjob{\typeout{\easychairstylesutcliffe}}
\everyjob{\typeout{\easychairstylecopyright}}
\everyjob{\typeout{\easychairstylebugs}}

\immediate\write10{\easychairstyleauthor}
\immediate\write10{\easychairstylerevision}
\immediate\write10{\easychairstylepurpose}
\immediate\write10{\easychairstylevoronkov}
\immediate\write10{\easychairstylesutcliffe}
\immediate\write10{\easychairstylecopyright}
\immediate\write10{\easychairstylebugs}


%
% Require LaTeX 2.09 or later
%

\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{easychair}[2008/06/19 v1.0]
\def\@tempa#1#2\@nil{\edef\@classname{#1}}
\expandafter\@tempa\@currnamestack{}{}{}\@nil
\ifx\@classname\@empty \edef\@classname{\@currname}\fi


%
% Debug
%

\def\easychairdebug#1{\gdef\@EasyDebug{#1}}
\def\@EasyDebug{}

\newif\ifdebug
\debugfalse

\DeclareOption{debug}{\debugtrue}


%
% Running heads definitions
%

\def\titlerunning#1{\gdef\@titleRunning{#1}}
\def\authorrunning#1{\gdef\@authorRunning{#1}}
\titlerunning{easychair: Running title head is undefined.}
\authorrunning{easychair: Running author head is undefined.}


%
% Decide between letter and A4 paper formats
% as well as orientation
%

% Default is 'letterpaper'
\def\paperformat#1{\gdef\@PaperFormat{#1}}
\def\@PaperFormat{letterpaper}

\newif\ifletterpaper
\newif\ifafourpaper

\letterpapertrue

\DeclareOption{letterpaper}{\paperformat{letterpaper}\afourpaperfalse}
\DeclareOption{a4paper}{\paperformat{a4paper}\afourpapertrue\letterpaperfalse}

% Default is portrait {}
\def\paperorientation#1{\gdef\@PaperOrientation{#1}}
\def\@PaperOrientation{}

\DeclareOption{portrait}{\paperorientation{}}
\DeclareOption{landscape}{\paperorientation{landscape}}

% Two sided running heads for titlerunning and author running
% twosided is the default
\newif\iftwosided
\twosidedfalse

\DeclareOption{onesided}{}
\DeclareOption{twosided}{\twosidedtrue}


%
% Decide between 1- or 2-column formats
%

\def\columnCount#1{\gdef\@ColumnCount{#1}}
\def\@ColumnCount{onecolumn}

\DeclareOption{onecolumn}{}
\DeclareOption{twocolumn}{\columnCount{twocolumn}}


%
% Decide on line spacing
%

\def\lineSpacing#1{\gdef\@LineSpacing{#1}}
\def\@LineSpacing{1.0}

\DeclareOption{singlespacing}{\lineSpacing{1.0}}
\DeclareOption{lineandhalfspacing}{\lineSpacing{1.5}}
\DeclareOption{doublespacing}{\lineSpacing{2.0}}

\DeclareOption{1.0}{\lineSpacing{1.0}}
\DeclareOption{1.5}{\lineSpacing{1.5}}
\DeclareOption{2.0}{\lineSpacing{2.0}}

\DeclareOption{1.0pt}{\lineSpacing{1.0}}
\DeclareOption{1.5pt}{\lineSpacing{1.5}}
\DeclareOption{2.0pt}{\lineSpacing{2.0}}


%
% Font point size; default is 11pt per Geoff Sutcliffe.
%
% The \headheight will have to be changed later accordingly
% such that fancyhdr does not complain it is too small.
%

\def\baseFontSize#1{\gdef\@BaseFontSize{#1}}
\def\headHeightSize#1{\gdef\@HeadHeightSize{#1}}

\def\@BaseFontSize{11pt}
\def\@HeadHeightSize{13.6pt}

\DeclareOption{8pt}{\PackageWarning{easychair}{Option '\CurrentOption' is not supported.}}
\DeclareOption{9pt}{\PackageWarning{easychair}{Option '\CurrentOption' is not supported.}}
%\DeclareOption{10pt}{\baseFontSize{10pt}\headHeightSize{12.0pt}}
\DeclareOption{10pt}{\PackageWarning{easychair}{Option '\CurrentOption' is not supported.}}
\DeclareOption{11pt}{\baseFontSize{11pt}\headHeightSize{13.6pt}}
\DeclareOption{12pt}{\baseFontSize{12pt}\headHeightSize{14.5pt}}


%
% Page sizing
%

%\newif\iffullpage
%\newif\ifsavetrees
%
%\DeclareOption{fullpage}{\fullpagetrue}
%\DeclareOption{savetrees}{\savetreestrue}


% Bark at any uknknown package option
\DeclareOption*{\PackageWarning{easychair}{Unknown option '\CurrentOption'}}
%\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}

%\ExecuteOptions{centertags,portrait,10pt,twoside,onecolumn,final}
\ExecuteOptions{}
\ProcessOptions\relax


%
% Required packages and classes.
%
% All must be standard as per most common LaTeX
% distributions.
%

% We are an article (more customized later)
\LoadClass[\@PaperFormat,\@PaperOrientation,\@ColumnCount,\@BaseFontSize,twoside]{article}
%\LoadClass[\@PaperFormat,\@PaperOrientation,\@ColumnCount,\@BaseFontSize]{article}


% Require UTF8 encoding, per Andrei Voronkov, to accomodate
% all sorts of author names.
%\RequirePackage[latin1]{inputenc}
\RequirePackage[utf8]{inputenc}

% All \urls will be hyperlinked and will deal properly with special characters
\RequirePackage{url}

% TOC/thumnamil LHS preview in the PDFs as well as active URLs and other cross-refs
\RequirePackage[\@PaperFormat]{hyperref}

% Traditional graphics processing
\RequirePackage{graphicx}
%\RequirePackage{pdflscape}
%\RequirePackage{lscape}

%% Fonts, generally more compact but preserving point size

% Pick "Times Roman" as a base font
\RequirePackage{mathptmx}

% Pick "Helvetica" as a "Sans-Serif" font
\RequirePackage{helvet}

% For algorithm and source code listings
\RequirePackage{listings}

%% Different Math and non-Math symbols and definitions

\RequirePackage{latexsym}
\RequirePackage{amsthm}
\RequirePackage{empheq}

%% Line spacing to be applied AFTER the above space saving packages

\renewcommand{\baselinestretch}{\@LineSpacing}

%% Final text printing area, per Geoff Sutcliffe

\newlength{\@MarginSize}
\setlength{\@MarginSize}{1in}

% Head height is dependent on the font point size
\setlength{\headheight}{\@HeadHeightSize}

\ifletterpaper
	\immediate\write10{easychair: Selecting letter paper margin sizes.}
	\RequirePackage[%
		%showframe,
		lmargin=1.1in,
		rmargin=1.1in,
		tmargin=\@MarginSize,
		bmargin=\@MarginSize,
		includefoot]{geometry}
\fi

\ifafourpaper
	\immediate\write10{easychair: Selecting A4 paper margin sizes.}
	\RequirePackage[%
		lmargin=\@MarginSize,
		rmargin=\@MarginSize,
		tmargin=1.35in,
		bmargin=1.35in,
		includefoot]{geometry}
\fi

\setlength{\textwidth}{16cm}
\setlength{\textheight}{9in}

%
% Volume
%

\RequirePackage{lastpage}

% e.g.
% \volumeinfo
%		{J. Bloe}   % editor(s)      #1
%		{1}         % No. of editors #2
%		{LICS 2008} % event title    #3
%		{1}         % volume number  #4
%		{4}         % issue          #5
%		{134}       % start page     #6

\newcommand{\volumeinfo}[6]{%
	\def\@makefntext##1{\noindent ##1}%
	\def\@Eds{ed.}%
	\ifnum #2>1 \def\@Eds{eds.} \fi%
	\footnotetext[0]{\sf #1 (\@Eds): #3, volume #4, issue: #5, pp. #6-\pageref{LastPage}}%
	\def\@makefntext##1{\noindent\@makefnmark##1}%
	\setcounter{page}{#6}}

% To ensure the footnotes are always at the bottom
\RequirePackage[bottom]{footmisc}


%
% Allow for more space to place floats.
%

\renewcommand{\topfraction}{0.95}
\renewcommand{\bottomfraction}{0.95}
\renewcommand{\textfraction}{0.05}
\renewcommand{\floatpagefraction}{0.8}


%
% Running heads and ``foots''
%

\RequirePackage{fancyhdr}
\pagestyle{fancy}

\fancyhead{}
\ifdebug
	\iftwosided
		\fancyhead[RE]{\overline{\@titleRunning}}
		\fancyhead[RO]{\overline{\@authorRunning}}
	\else
		\fancyhead[LO,LE]{\begin{math}\overline{\mbox{\@titleRunning}}\end{math}}
		\fancyhead[RO,RE]{\begin{math}\overline{\mbox{\@authorRunning}}\end{math}}
	\fi
\else
	\iftwosided
		\fancyhead[RE]{\@titleRunning}
		\fancyhead[RO]{\@authorRunning}
	\else
		\fancyhead[LO,LE]{\@titleRunning}
		\fancyhead[RO,RE]{\@authorRunning}
	\fi
\fi

\fancyfoot{}
\ifdebug
	\fancyfoot[CO,CE]{\underline{\thepage}}
	\renewcommand{\headrulewidth}{1pt}
	\renewcommand{\footrulewidth}{1pt}
\else
	\fancyfoot[CO,CE]{\thepage}
	\renewcommand{\headrulewidth}{0pt}
	\renewcommand{\footrulewidth}{0pt}
\fi

% Suppress the default date
\date{}

\let\oldmaketitle=\maketitle
\def\@maketitle{%
	\newpage
	\null
	\vspace{-2.5cm}
	\begin{center}%
		\let \footnote \thanks
		{\LARGE{\@title}\par}
		\vskip 0.5\baselineskip
		\begin{tabular}[t]{c}%
		\@author
		\end{tabular}\par
		%\vskip 0.5\baselineskip
		\@date
	\end{center}%
	\par
	%\vskip \baselineskip
}

% Tighten up bibliography
\let\oldthebibliography=\thebibliography
\let\endoldthebibliography=\endthebibliography
\renewenvironment{thebibliography}[1]
{
	\small
	\begin{oldthebibliography}{#1}
		\setlength{\parskip}{2pt}
		\setlength{\itemsep}{0pt}
}
{
  \end{oldthebibliography}
}

\endinput

% EOF
