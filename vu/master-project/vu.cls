\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{vu}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{report}}

\ProcessOptions

\LoadClass[11pt,a4paper]{report}

% AMS math fonts
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}

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

% AMS theorem styles
\usepackage{amsthm}

% Theorem styles
\theoremstyle{definition}
\newtheorem{definition}{Definition}

% Additional list environments
\usepackage{paralist}
\setdefaultenum{i.}{a.}{}{}

% TODO: title page layout
% TODO: bibliography style
% http://tug.ctan.org/tex-archive/macros/latex/contrib/ucthesis/

\endinput
