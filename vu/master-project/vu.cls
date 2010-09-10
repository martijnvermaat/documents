\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{vu}[2010/08/05 A simple VU University Msc thesis class]

% This class is quite specific to my (Martijn Vermaat) needs...

\makeatletter
\newif\if@vucolors
  \@vucolorsfalse
\DeclareOption{color}{\@vucolorstrue}
\makeatother

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{report}}

\ProcessOptions

\LoadClass[10pt,b5paper,twoside,openright]{report}

% Paper format 'Royal'
%\usepackage[nohead,
%  vmarginratio=2:3,hmarginratio=1:1,
%  papersize={15.593cm,23.389cm},total={11.0cm,19.5cm}]{geometry}
% Paper format 'US Commerce'
\usepackage[nohead,
  vmarginratio=2:3,hmarginratio=1:1,
  papersize={6in,9in},total={11.0cm,19.0cm}]{geometry}

% AMS math fonts
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}

% For \iddots
\usepackage{mathdots}

% For nice inline fractions
\usepackage{xfrac}

% TeX Gyre Pagella (like Palatino)
%\usepackage{tgpagella}
%\usepackage{qpxmath}

% TeX Gyre Termes (like Times)
\usepackage{tgtermes}
\usepackage{qtxmath}

% txtt for tt
\renewcommand{\ttdefault}{txtt}

% Computer Modern for tt
%\renewcommand{\ttdefault}{cmtt}

% Helvetica for sans serif
%\renewcommand{\sfdefault}{qhv}
\usepackage[scaled=0.95]{helvet}

% Use T1 font encoding
\usepackage[T1]{fontenc}

% Abstract
\usepackage{abstract}
\renewcommand{\abstractnamefont}{\normalfont\sc}

% Headings
\usepackage{fancyhdr}
\pagestyle{fancy}

\fancyhf{} % reset headers and footers
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0pt}

% Redefine plain page style
\fancypagestyle{plain}{%
  %\fancyhead{}
  \fancyhf{}
  \renewcommand{\headrulewidth}{0pt}
  \renewcommand{\footrulewidth}{0pt}
}

\renewcommand{\chaptermark}[1]{\markboth{\textsc{\chaptername
     \ \thechapter}\hskip 1em {\emph{#1}}}{}}
%\renewcommand{\sectionmark}[1]{\markright{\textsc{Section
%      \thesection}\hskip 1em #1}}
\renewcommand{\sectionmark}[1]{\markright{\textsc{\thesection}\hskip
    1em {\emph{#1}}}}

\fancyfoot[RE]{\leftmark}
\fancyfoot[LO]{\rightmark}
\fancyfoot[LE,RO]{\textsc{\thepage}}

% Cleared left pages must be really empty
\let\origdoublepage\cleardoublepage
\newcommand{\clearemptydoublepage}{%
  \clearpage
      {\pagestyle{empty}\origdoublepage}%
}
\let\cleardoublepage\clearemptydoublepage

% Empty page style in table of contents
% hmm get empty page style for toc, this doesn't seem to work
\addtocontents{toc}{\protect\thispagestyle{empty}}

% Chapter and section title styles
\usepackage{titlesec}

% Smallcaps for 'Chapter n' and section numbering
\titleformat{\chapter}[display]
{\normalfont\huge}{\sc\chaptertitlename\ \thechapter}{20pt}{\Huge}
%\titleformat{\section}
%{\normalfont\Large}{\sc Section\ \thesection}{1em}{}
\titleformat{\section}
{\normalfont\Large}{\sc \thesection}{1em}{}
\titleformat{\subsection}
{\normalfont\large}{\sc\thesubsection}{1em}{}
\titleformat{\subsubsection}
{\normalfont\normalsize\bfseries}{\sc\thesubsubsection}{1em}{}
\titleformat{\paragraph}[runin]
{\normalfont\normalsize\bfseries}{\theparagraph}{1em}{}
\titleformat{\subparagraph}[runin]
{\normalfont\normalsize\bfseries}{\thesubparagraph}{1em}{}
\titlespacing*{\chapter} {0pt}{50pt}{40pt}
\titlespacing*{\section} {0pt}{3.5ex plus 1ex minus .2ex}{2.3ex plus .2ex}
\titlespacing*{\subsection} {0pt}{3.25ex plus 1ex minus .2ex}{1.5ex plus .2ex}
\titlespacing*{\subsubsection}{0pt}{3.25ex plus 1ex minus .2ex}{1.5ex plus.2ex}
\titlespacing*{\paragraph} {0pt}{3.25ex plus 1ex minus .2ex}{1em}
\titlespacing*{\subparagraph} {\parindent}{3.25ex plus 1ex minus .2ex}{1em}

% Dutch style of paragraph formatting, i.e. no indents
%\setlength{\parskip}{1.3ex plus 0.2ex minus 0.2ex}
%\setlength\parskip{\bigskipamount}
\setlength\parskip{\medskipamount}
\setlength{\parindent}{0pt}

% Linespacing
\usepackage[onehalfspacing]{setspace}

% Footnotes
\usepackage[perpage,hang,flushmargin]{footmisc}

% Section numbering in margin
%\usepackage{sectsty}
%\makeatletter\def\@seccntformat#1{\protect\makebox[0pt][r]{\csname
%    the#1\endcsname\hspace{12pt}}}\makeatother

% Natbib for the bibliography, always. sort&compress will make i.e. [1-5,7].
%\usepackage[square,numbers,sort&compress]{natbib}
\usepackage[round,authoryear,longnamesfirst]{natbib}
%\usepackage[numbers]{natbib}
\bibliographystyle{plainnat}
%\bibliographystyle{dcu}
%\setlength{\bibhang}{0ex}

% Customizable theorem environments
\usepackage[amsmath,thmmarks]{ntheorem}

%\makeatletter
%\newtheoremstyle{definition}
%{\item[\hskip\labelsep \theorem@headerfont ##1\ ##2\theorem@separator]}
%{\item[\hskip\labelsep \theorem@headerfont ##1\ ##2\ (##3)\theorem@separator]}
%\makeatother

\theoremstyle{plain}
\theoremheaderfont{\sc}
\theorembodyfont{\normalfont}
\theoremsymbol{\ensuremath{\ast}}
\theoremseparator{.}
\newtheorem{definition}{Definition}

\theoremstyle{plain}
\theoremheaderfont{\sc}
\theorembodyfont{\normalfont}
\theoremsymbol{}
\theoremseparator{.}
\newtheorem{proposition}{Proposition}

\theoremstyle{plain}
\theoremheaderfont{\sc}
\theorembodyfont{\normalfont}
\theoremsymbol{}
\theoremseparator{.}
\newtheorem{lemma}{Lemma}

\theoremstyle{nonumberplain}
\theoremheaderfont{\sc}
\theorembodyfont{\upshape}
%\theoremsymbol{\ensuremath{_\blacksquare}}
\theoremsymbol{\ensuremath{\Box}}
\theoremseparator{.}
\newtheorem{proof}{Proof}

% Figure captions
\usepackage[labelfont={sc,footnotesize},textfont=footnotesize,labelsep=period,margin=15pt]{caption}

% Figure numbering
%\renewcommand{\thefigure}{\arabic{figure}}
\numberwithin{figure}{chapter}

% Additional list environments
\usepackage{paralist}
\setdefaultenum{\sc i.}{a.}{}{}

\usepackage{url}
%% Define a new 'leo' style for the package that will use a smaller
%% font.
\makeatletter
\def\url@leostyle{%
  \@ifundefined{selectfont}{\def\UrlFont{\sf}}{\def\UrlFont{\small\ttfamily}}}
\makeatother
%% Now actually use the newly defined style.
\urlstyle{leo}

\makeatletter
\def\makefrontmatter{
  \newpage
    \thispagestyle{empty}
    \null\vfil
    \vspace{2cm}
    {\Huge \@title \par}
    \vspace{6cm}
    {\@author \par}
    \vfil\null
    \pagenumbering{alph}
    \setcounter{page}{1}
  \newpage
    \thispagestyle{empty}
    \null\vfil\null
}
\makeatother

\makeatletter
\def\maketitle{
  \newpage
    \thispagestyle{empty}
    \null\vfil
    \begin{center}
    {VU UNIVERSITY AMSTERDAM \par}
    \vspace{2cm}
    {\Huge \@title \par}
    \vspace{3cm}
    {THESIS \par}
    \vspace{2cm}
    {submitted in partial fulfillment of the requirements for\\
      the degree of Master of Science by research at\\
      the VU University Amsterdam \par}
    \vspace{1cm}
    {by \@author \par}
    \vspace{1cm}
    {\sc \@date \par}
    \vspace{2cm}
    {\renewcommand{\arraystretch}{1.1}
      \renewcommand{\tabcolsep}{35pt}
      \begin{tabular}{c c}
        {\sc supervisor} & {\sc second reader}\\
        {\sc dr.} R.D.A.\ Hendriks & {\sc dr.} R.C.\ de Vrijer
    \end{tabular}}
    \end{center}
    \vfil\null
    \pagenumbering{alph}
    \setcounter{page}{3}
  \newpage
    \thispagestyle{empty}
    \null\vfil
    \vspace{9cm}
    \if@vucolors
      {\includegraphics[draft=false,width=5cm]{logos/vu-logo-en}\par}
    \else
      {\includegraphics[draft=false,width=5cm]{logos/vu-logo-en-grayscale}\par}
    \fi
    \vspace{10pt}
    {Typeset using \LaTeX\ by Leslie Lamport, based on
      \TeX\ by Donald Knuth. \par}
    {Creative Commons Attribution logo by Sebastian Pipping. \par}
    {\emph{Oiseau d'infini} cover by Bastiaan Terhorst, \url{http://perceptor.nl}. \par}
    \vspace{10pt}
    {\copyright\ 2010 Martijn Vermaat \par}
    \vspace{10pt}
    % CC Logo by Sebastian Pipping, http://blog.hartwork.org/?p=52
    % this is ugly (255pt does not completely fill the page)
    \pagenumbering{alph}
    \setcounter{page}{4}
    {\begin{singlespace}\begin{tabular}{c p{255pt}}
      \raisebox{-10pt}{\includegraphics[draft=false,scale=1.0]{logos/cc-by}}
      %\includegraphics[draft=false,scale=1.0]{logos/cc-by}
      &
      This work is licensed under the Creative Commons
      Attribution 3.0 Netherlands License. To view a copy of this
      license, visit
      \url{http://creativecommons.org/licenses/by/3.0/nl/} or send
      a letter to Creative Commons, 171 Second Street, Suite 300,
      San Francisco, California 94105, US.
    \end{tabular}\end{singlespace}\par}
    \vfil\null
}
\makeatother

\usepackage{graphicx}

\endinput
