\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{vu}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{report}}

\ProcessOptions

\LoadClass[11pt,a4paper]{report}

% AMS math fonts
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}

% For \iddots
\usepackage{mathdots}

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

% A4 page
\usepackage{a4}

% Headings
%\pagestyle{headings}

% Chapter and section title styles
\usepackage{titlesec}

% Smallcaps for 'Chapter n' and section numbering
% TODO: smallcaps for footnote and page numbering
\titleformat{\chapter}[display]
{\normalfont\huge}{\sc\chaptertitlename\ \thechapter}{20pt}{\Huge}
\titleformat{\section}
{\normalfont\Large}{\sc Section\ \thesection}{1em}{}
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

% Section numbering in margin
%\usepackage{sectsty}
%\makeatletter\def\@seccntformat#1{\protect\makebox[0pt][r]{\csname
%    the#1\endcsname\hspace{12pt}}}\makeatother

% Natbib for the bibliography, always. sort&compress will make i.e. [1-5,7].
%\usepackage[square,numbers,sort&compress]{natbib}
%\usepackage[authoryear,sort]{natbib}
\usepackage[numbers]{natbib}
\setlength{\bibhang}{0ex}

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

% TODO: style propositions
\theoremstyle{nonumberplain}
\theoremheaderfont{\sc}
\theorembodyfont{\upshape}
%\theoremsymbol{\ensuremath{_\blacksquare}}
\theoremsymbol{\ensuremath{\Box}}
\theoremseparator{.}
\newtheorem{proof}{Proof}

% Additional list environments
\usepackage{paralist}
\setdefaultenum{i.}{a.}{}{}

% TODO: title page layout
% TODO: bibliography style
% http://tug.ctan.org/tex-archive/macros/latex/contrib/ucthesis/

\makeatletter
\def\makefrontmatter{
  \newpage
    \thispagestyle{empty}
    \null\vfil
    \vspace{2cm}
    {\Huge \@title (DRAFT) \par}
    \vspace{6cm}
    {\@author \par}
    \vfil\null
    \setcounter{page}{1}
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
    {\Huge \@title (DRAFT) \par}
    \vspace{3cm}
    {THESIS \par}
    \vspace{2cm}
    {submitted for the degree of Master of Science by research at\\
      the VU University Amsterdam \par}
    \vspace{1cm}
    {by \@author \par}
    \vspace{1cm}
    {\sc \@date \par}
    \vspace{2cm}
    {\renewcommand{\arraystretch}{1.1}
      \renewcommand{\tabcolsep}{50pt}
      \begin{tabular}{c c}
        {\sc supervisor} & {\sc second reader}\\
        {\sc dr.} R.D.A.\ Hendriks & {\sc dr.} R.C.\ de Vrijer
    \end{tabular}}
    \end{center}
    \vfil\null
    \setcounter{page}{1}
}
\makeatother

\usepackage{graphicx}

\endinput
