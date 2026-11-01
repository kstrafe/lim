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
syn match limKeyword +#[[:alpha:]_][^[:space:]();"'`,@#]*+
syn match limGenerated +#generate\ze\%($\|[[:space:]();"'`,#]\)+
syn match limExternal +[[:alpha:]_][[:alnum:]_.-]*@[^[:space:]();"'`,#]\++
" A leading @ resolves a source name; embedded @ is ordinary identifier text.
syn match limQualified +\%(^\|[[:space:]('`]\)\@<=@[^[:space:]();"'`,#]\++
syn match limGenerated +#generated-context\ze\%($\|[[:space:]();"'`,#]\)+
" Type properties are declaration annotations, not callable forms.
syn match limTypeProperty +#\%(linear\|repr-c\)\ze\%($\|[[:space:]();"'`,@#]\)+

" Match complete tokens, including the sigil. In particular, #u64 is a type
" but #u64::add-wrap is an operator and an unprefixed u64 is a user identifier.
syn match limType +#\%(bool\|char\|u8\|u16\|u32\|u64\|u128\|usize\|i8\|i16\|i32\|i64\|i128\|isize\|f32\|f64\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limTypeForm +#\%(ref\|ref-mut\|ptr\|ptr-mut\|array\|slice\|slice-mut\|tuple\|pin-ref\|pin-ref-mut\|pin-own\|pin-shared-own\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limOperator +#\%(bool\|char\|u8\|u16\|u32\|u64\|u128\|usize\|i8\|i16\|i32\|i64\|i128\|isize\|f32\|f64\)::[^[:space:]();"'`,@#]\++
syn match limDeclaration +#\%(alias\|theorem\|math-definition\|math-opaque\|math-inductive\|fn\|extern-fn\|struct\|enum\|distributed-enum\|enum-contribute\|type\|static\|let\|let-mut\|const\|export\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limProof +#\%(universes\|parameters\|parameter\|parameter-of\|indices\|mutual\|statement\|proof\|pt-prop\|pt-sort\|pt-type\|pt-pi\|pt-lambda\|pt-let\|pt-sigma\|pt-app\|pt-use\|pt-level-succ\|pt-level-max\|pt-level-imax\|pt-nat\|pt-false\|pt-foundation-choice\|pt-foundation-propext\|pt-foundation-quot-sound\|pt-self\|pt-self-at\|pt-zero\|pt-succ\|pt-nat-literal\|pt-numeral\|pt-construct\|pt-project\|pt-induct\|pt-recur\|pt-mutual-induct\|pt-nested-induct\|pt-case\|pt-nat-induct\|pt-eq\|pt-refl\|pt-eq-elim\|pt-pair\|pt-first\|pt-second\|pt-quot\|pt-quot-induct\|pt-quot-lift\|pt-quot-make\|pt-program\|pt-certificate\|proof-and\|proof-or\|proof-not\|proof-implies\|proof-calls-directly\|proof-calls-transitively\|proof-calls-before\|proof-calls-when\|proof-no-effects\|proof-only-unsafe\|proof-stack-at-most\|proof-for-all\|proof-eq\|proof-contract\|proof-requires-validation\|proof-result\|proof-old\|proof-no-overflow\|proof-with-invariants\|proof-loop-limit\|proof-sorted\|proof-permutation\|proof-allocation\|proof-io\|proof-global-write\|proof-unsafe\|proof-external\|proof-asm\|proof-mutation\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limConditional +#\%(if\|if-let\|match\|case\|case-pin\|case-pin-mut\|case-ref\|case-ref-mut\|let-else\|else\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limRepeat +#\%(loop\|while\|while-let\|for\|for-range\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limControl +#\%(return\|break\|break-to\|continue\|continue-to\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limUnsafe +#\%(unsafe\|unsafe-call\|unsafe-fn\|unsafe-impl\|unstable\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limPin +#\%(pin\|pin-shared\|pin-share\|pin-share-clone\|pin-shared-borrow\|pin-shared-borrow-mut\|pin-shared-release\)\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limGeneratorKeyword +#gn\%(-[^[:space:]();"'`,@#]\+\)\?\ze\%($\|[[:space:]();"'`,@#]\)+
syn match limCfg +#cfg-[^[:space:]();"'`,@#]\++
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
syn cluster limForms contains=limProof,limKeyword,limGenerated,limExternal,limQualified,limTypeProperty,limType,limTypeForm,limOperator,limDeclaration,limConditional,limRepeat,limControl,limUnsafe,limPin,limGeneratorKeyword,limCfg,limNumber,limString,limCharacter,limComment
syn region limNest1 transparent start="(" end=")" contains=@limForms,limNest2,limParen1
syn region limNest2 transparent start="(" end=")" contained contains=@limForms,limNest3,limParen2
syn region limNest3 transparent start="(" end=")" contained contains=@limForms,limNest4,limParen3
syn region limNest4 transparent start="(" end=")" contained contains=@limForms,limNest5,limParen4
syn region limNest5 transparent start="(" end=")" contained contains=@limForms,limNest6,limParen5
syn region limNest6 transparent start="(" end=")" contained contains=@limForms,limNest1,limParen1

hi def link limComment Comment
hi def link limString String
hi def link limEscape SpecialChar
hi def link limCharacter Character
hi def link limKeyword Keyword
hi def link limGenerated Special
hi def link limExternal Identifier
hi def link limQualified Special
hi def link limTypeProperty Keyword
hi def link limType Type
hi def link limTypeForm Type
hi def link limOperator Operator
hi def link limDeclaration StorageClass
hi def link limProof Keyword
hi def link limConditional Conditional
hi def link limRepeat Repeat
hi def link limControl Statement
hi def link limUnsafe Exception
hi def link limPin Keyword
hi def link limGeneratorKeyword PreProc
hi def link limCfg PreProc
hi def link limNumber Number
hi def link limParen1 Delimiter
hi def link limParen2 Identifier
hi def link limParen3 Special
hi def link limParen4 Statement
hi def link limParen5 Type
hi def link limParen6 Constant

let b:current_syntax = 'lim'
