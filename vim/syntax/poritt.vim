" Vim syntax file
" Language:		PoriTT
" Maintainer:		Oleg Grenrus <oleg.grenrus@iki.fi>
" Original Author:	Oleg Grenrus <oleg.grenrus@iki.fi>

" quit when a syntax file was already loaded
if exists("b:current_syntax")
  finish
endif

" identifiers (no default highlighting)
syn match mttIdentifier "\<[a-zA-Z0-9_']+\>" contains=@NoSpell

" identifiers which start with colon : are labels
syn match mttLabel ":[a-zA-Z0-9_']*\>"

" identifiers which start with dot . are selectors
syn match mttSelector "\.[a-z][a-zA-Z0-9_']*\>"

" string literals
syn match mttString "\"[^\"]*\""

" Reserved symbols--cannot be overloaded.
syn match mttDelimiter  "(\|)\|\[\|\]\||\|;\|_\|{\|}\|\$\|#"

" Keyword definitions.
syn keyword mttStmt    define eval type info inline macro include section options fail
syn keyword mttType    forall -> exists * U mu Desc Code Unit
syn keyword mttKeyword let in switch ind con `1 `S `X indDesc tt

syn keyword mttOperator : = \\ ,

" Comments
syn match mttComment    /--.*$/

" Hole
syn match mttHole "?[a-zA-Z0-9_']*\>"

" Define the default highlighting.
" Only when an item doesn't have highlighting yet

hi def link mttDelimiter			  Delimiter
hi def link mttStmt             PreProc
hi def link mttType             Type
hi def link mttKeyword          Statement
hi def link mttComment          Comment
hi def link mttOperator         Operator
hi def link mttLabel    			  Special
hi def link mttSelector         Function
hi def link mttString           Constant
hi def link mttHole             Error

" Available groups
" https://vimdoc.sourceforge.net/htmldoc/syntax.html#{group-name}

let b:current_syntax = "poritt"

" Options for vi: ts=8 sw=2 sts=2 nowrap noexpandtab ft=vim
