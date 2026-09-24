" Vim syntax file for Lim.
if exists('b:current_syntax')
  finish
endif

syn case match

" Comments: semicolon comments and bare hash comment lines.
syn match limComment ";.*$" contains=@Spell
syn match limComment "^\s*#\s.*$" contains=@Spell

" Strings and character literals. Hash-prefixed character names and Unicode
" escapes are kept together as one token.
syn region limString start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=limEscape,@Spell
syn match limEscape "\\\\[nrt\\\\\"]\|\\\\u{[[:xdigit:]]\+}" contained
syn match limCharacter "#\\\%(u{[[:xdigit:]]\+}\|[[:alpha:]][[:alnum:]_-]*\|.\)"

" Lim forms, operators, and generator operations use a leading #.
syn match limKeyword "#[[:alpha:]_][[:alnum:]_+*.<>!?-]*"
syn match limGenerated "@[[:alpha:]_][[:alnum:]_+*.<>!?-]*"

" Explicit scalar types.
syn keyword limType bool char u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize f32 f64
syn match limNumber "\<\d[[:alnum:]_]*\>"
syn match limNumber "\<\d[[:digit:]_]*\.\d[[:digit:]_]*\([eE][+-]\?[[:digit:]_]*\)\?[fF]\?\(32\|64\)\?\>"

" Cycle delimiter groups by nesting depth. The six groups intentionally
" link to common rainbow colors where available; the plugin can override them.
syn match limParen1 "[()]" contained
syn match limParen2 "[()]" contained
syn match limParen3 "[()]" contained
syn match limParen4 "[()]" contained
syn match limParen5 "[()]" contained
syn match limParen6 "[()]" contained
syn region limNest1 transparent start="(" end=")" contains=limKeyword,limGenerated,limType,limNumber,limString,limCharacter,limComment,limNest2,limParen1
syn region limNest2 transparent start="(" end=")" contained contains=limKeyword,limGenerated,limType,limNumber,limString,limCharacter,limComment,limNest3,limParen2
syn region limNest3 transparent start="(" end=")" contained contains=limKeyword,limGenerated,limType,limNumber,limString,limCharacter,limComment,limNest4,limParen3
syn region limNest4 transparent start="(" end=")" contained contains=limKeyword,limGenerated,limType,limNumber,limString,limCharacter,limComment,limNest5,limParen4
syn region limNest5 transparent start="(" end=")" contained contains=limKeyword,limGenerated,limType,limNumber,limString,limCharacter,limComment,limNest6,limParen5
syn region limNest6 transparent start="(" end=")" contained contains=limKeyword,limGenerated,limType,limNumber,limString,limCharacter,limComment,limNest1,limParen1

hi def link limComment Comment
hi def link limString String
hi def link limEscape SpecialChar
hi def link limCharacter Character
hi def link limKeyword Keyword
hi def link limGenerated Special
hi def link limType Type
hi def link limNumber Number
hi def link limParen1 Delimiter
hi def link limParen2 Identifier
hi def link limParen3 Special
hi def link limParen4 Statement
hi def link limParen5 Type
hi def link limParen6 Constant

let b:current_syntax = 'lim'
