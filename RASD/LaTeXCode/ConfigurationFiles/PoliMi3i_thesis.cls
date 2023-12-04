% A LaTeX template for MSc Thesis submissions to 
% Politecnico di Milano (PoliMi) - School of Industrial and Information Engineering
%
% P. F. Antonietti, S. Bonetti, A. Gruttadauria, G. Mescolini, A. Zingaro
%
% Last Revision: October 2021
%
% Copyright 2021 Politecnico di Milano, Italy. Inc. All rights reserved

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{ConfigurationFiles/PoliMi3i_thesis}[2021/6/30 PoliMi3i thesis submission class]
\ProcessOptions\relax

%--------------------------------------------------------------------------
%	HANDLING THE STYLE OF THE THESIS
%--------------------------------------------------------------------------
\LoadClass[12pt, twoside]{book} % 12 pt font, two-sided book style
\RequirePackage[a4paper, includehead, headheight=0.6cm, inner=3.0cm ,outer=2.0cm, top=2.5cm, bottom=2.5cm]{geometry}

\RequirePackage[bf, font=onehalfspacing]{caption} % caption: FIG in bold, 1.5 line spacing in figure and table captions
\newcommand{\thesisspacing}{\onehalfspacing}

% Define new command: numbered and un-numbered chapter in Polimi style. 

\let\latexchapter\chapter
%! suppress = MightBreakTexify
\renewcommand{\chapter}{\@ifstar{\polimichapterstar}{\polimichapter}}

\newcommand{\polimichapter}[1]{
    \cleardoublepage % To make sure the previous headers are passed
    \phantomsection % To help hyperref link to the right page
    \latexchapter{#1}
    \renewcommand{\headrulewidth}{0pt} %removing the horizontal line in the header
    \fancyhead[LO, RE]{ \textbf{\textcolor{bluepoli}\thechapter\hsp\textcolor{bluepoli}{|   }\hsp \leftmark}}% Header
    \fancyhead[LE, RO]{\thepage}
    \vspace{-1cm}
}

\newcommand{\polimichapterstar}[1]{
    \cleardoublepage % To make sure the previous headers are passed
    \phantomsection % To help hyperref link to the right page
    \latexchapter*{#1}
    \renewcommand{\headrulewidth}{0pt} %removing the horizontal line in the header
    \addcontentsline{toc}{chapter}{#1} % Also adds the chapter name to the Contents
    \fancyhead[LO, RE]{ \bfseries \textcolor{bluepoli}{|   } #1} % Header \textbf{\leftmark} \hspace{1mm}}
    \fancyhead[LE, RO]{\thepage}
    \vspace{-1cm}
}

% Define new command: start preamble
\newcommand{\startpreamble}{
    \pagestyle{fancy} % Change the header style
    \fancyhf{}% Clear header and footer
    \renewcommand{\chaptermark}[1]{\markboth{##1}{}} % Getting the chapter name right
    \rhead{\thepage} % Page number at the right of the header
    \frontmatter % Use roman page numbering style (i, ii, iii, iv...) for the preamble pages
    \thesisspacing % Double or single spacing
}

%------------------------------------------------------------------------
%	BUILDING THE TITLE PAGE
%------------------------------------------------------------------------

% Define new command: adding background picture (halo) on bottom left (used for empty pages)
\newcommand\BackgroundPic{
    \put(-150,-200){%
        \parbox[b][\paperheight]{\paperwidth}{%
            \vfill
            \centering
            \transparent{0.4}
            \includegraphics[width=0.85\paperwidth]{images/raggiera_polimi}
            \vfill
        }}}

% Define new command: adding background picture (halo) on top right (used for cover page)
\newcommand\BackgroundPicTR{% Adding background picture on top right 
    \put(200,330){%
        \parbox[b][\paperheight]{\paperwidth}{%
            \vfill
            \centering
            \transparent{0.4}
            \includegraphics[width=0.70\paperwidth]{images/raggiera_polimi}
            \vfill
        }}}

\RequirePackage{xkeyval} % Handling keyword options.

% Define keys for title pages
\newif\if@cosupervisorexist\@cosupervisorexistfalse
\define@key[OIST]{title}{title}{\def\thesistitle{#1}}
\define@key[OIST]{title}{name1}{\def\nameA{#1}}
\define@key[OIST]{title}{name2}{\def\nameB{#1}}
\define@key[OIST]{title}{name3}{\def\nameC{#1}}
\define@key[OIST]{title}{academicyear}{\def\academicyear{#1}}

\providecommand{\puttitle}{}
\renewcommand{\puttitle}[1]{
    \@puttitle{}{#1}
}

\providecommand{\@puttitle}{}
\renewcommand{\@puttitle}[2]{%
    \setkeys[OIST]{title}{#2}

    \begin{titlepage}
        \AddToShipoutPicture*{\BackgroundPicTR}
        \vfill
        \begin{minipage}{0.95\textwidth}
            \includegraphics[trim={1.2cm 0 0 0},clip, width=0.7\textwidth]{images/02_ING_IND_INFORMAZIONE_COL_POSITIVO}
            \hfill
            \\
            \vspace{2.5cm}
            \\
            {{\color{bluepoli} \singlespacing \huge \bfseries \thesistitle \par}}
            \vspace{1.5cm}
            {\color{black} \Large {Author(s):} \bfseries{\nameA}} \\ \\
            \vspace{0.51cm}
            {\color{black} \hspace{6.3em} \Large \bfseries{\nameB}} \\
            \vspace{0.51cm}
            {\color{black} \hspace{6.3em} \Large \bfseries{\nameC}} \\
        \end{minipage}
        \\
        \vspace*{\fill}
        \\
        \begin{minipage}{0.85\textwidth}
            \normalsize{
                Academic Year: {\academicyear}
            }
        \end{minipage}
    \end{titlepage}
}

\newcommand\blankpage{%
    \null
    \AddToShipoutPicture*{\BackgroundPic}
    \thispagestyle{empty}%
    \addtocounter{page}{-1}%
    \newpage
}
