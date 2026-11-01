" Run from any directory: nvim --headless -u NONE -i NONE -n -S <this file>
let s:root = fnamemodify(expand('<sfile>:p'), ':h:h')
execute 'source ' . fnameescape(s:root . '/syntax/lim.vim')
syntax sync fromstart

function! s:check(token, expected) abort
  " Test every byte, including punctuation and the leading sigil, at multiple
  " nesting depths (the rainbow delimiter groups cycle after six levels).
  for depth in [0, 1, 2, 6, 7, 12]
    call setline(1, repeat('(', depth) . a:token . repeat(')', depth))
    " Restart the syntax scan after replacing the fixture line.
    call synID(1, 1, 1)
    for column in range(depth + 1, depth + strlen(a:token))
      call assert_equal(a:expected, synIDattr(synID(1, column, 1), 'name'),
            \ a:token . ' at depth ' . depth . ', column ' . column)
    endfor
  endfor
endfunction

for s:type in ['bool', 'char', 'u8', 'u16', 'u32', 'u64', 'u128', 'usize',
      \ 'i8', 'i16', 'i32', 'i64', 'i128', 'isize', 'f32', 'f64']
  call s:check('#' . s:type, 'limType')
  call s:check(s:type, '')
endfor
for [s:token, s:group] in [
      \ ['#ref-mut', 'limTypeForm'], ['#slice', 'limTypeForm'],
      \ ['#pin', 'limPin'], ['#pin-shared', 'limPin'],
      \ ['#pin-ref', 'limTypeForm'], ['#pin-ref-mut', 'limTypeForm'],
      \ ['#case-ref', 'limConditional'], ['#case-ref-mut', 'limConditional'],
      \ ['#pin-own', 'limTypeForm'], ['#pin-borrow', 'limKeyword'],
      \ ['#pin-borrow-mut', 'limKeyword'], ['#pin-custom', 'limKeyword'],
      \ ['#u64::add-wrap', 'limOperator'], ['#u128::div', 'limOperator'],
      \ ['#u128::rem', 'limOperator'], ['#i8::mul-saturate', 'limOperator'],
      \ ['#u64::eq', 'limOperator'], ['#u32::bit-and', 'limOperator'],
      \ ['#bool::or', 'limOperator'], ['#fn', 'limDeclaration'],
      \ ['#let-mut', 'limDeclaration'], ['#case', 'limConditional'],
      \ ['#case-pin', 'limConditional'], ['#case-pin-mut', 'limConditional'],
      \ ['#let-else', 'limConditional'], ['#while', 'limRepeat'],
      \ ['#return', 'limControl'], ['#unsafe', 'limUnsafe'],
      \ ['#alias', 'limDeclaration'], ['#unstable', 'limUnsafe'],
      \ ['#gn', 'limGeneratorKeyword'], ['#gn-for-each', 'limGeneratorKeyword'],
      \ ['#cfg-if', 'limCfg'], ['#generate', 'limGenerated'],
      \ ['#vec', 'limKeyword'], ['#cell', 'limKeyword'],
      \ ['collection@Vec', 'limExternal'], ['#export', 'limDeclaration'],
      \ ['@Value', 'limQualified'], ['@collection@Vec', 'limQualified'],
      \ ['#generated-context', 'limGenerated'],
      \ ['#call', 'limKeyword'], ['#u64-custom', 'limKeyword'],
      \ ['#enum-literal', 'limKeyword'], ['#struct-literal', 'limKeyword'],
      \ ['#return-value', 'limKeyword'], ['42u64', 'limNumber'],
      \ ['u64-value', ''], ['"#u64 #return"', 'limString'],
      \ ['; #u64 #return', 'limComment'], ['#\newline', 'limCharacter']]
  " Comments must not swallow the closing delimiters in the nesting fixture.
  if s:group ==# 'limComment'
    call setline(1, s:token)
    call assert_equal(s:group, synIDattr(synID(1, 3, 1), 'name'))
  else
    call s:check(s:token, s:group)
  endif
endfor

" Canonical proof forms use exact tokens; similar names remain generic keywords.
call s:check('#theorem', 'limDeclaration')
call s:check('#math-definition', 'limDeclaration')
call s:check('#math-inductive', 'limDeclaration')
for s:proof in [
      \ 'universes', 'parameters', 'parameter', 'parameter-of', 'statement', 'proof',
      \ 'pt-prop', 'pt-sort', 'pt-type', 'pt-pi', 'pt-lambda', 'pt-sigma', 'pt-app', 'pt-use',
      \ 'pt-level-succ', 'pt-level-max', 'pt-level-imax', 'pt-nat', 'pt-false', 'pt-self', 'pt-zero',
      \ 'pt-succ', 'pt-numeral', 'pt-construct', 'pt-induct', 'pt-nat-induct',
      \ 'pt-eq', 'pt-refl', 'pt-eq-elim', 'pt-pair', 'pt-first', 'pt-second',
      \ 'pt-program', 'pt-certificate',
      \ 'proof-and',
      \ 'proof-or',
      \ 'proof-not',
      \ 'proof-implies',
      \ 'proof-calls-directly',
      \ 'proof-calls-transitively',
      \ 'proof-calls-before',
      \ 'proof-calls-when',
      \ 'proof-no-effects',
      \ 'proof-only-unsafe',
      \ 'proof-stack-at-most',
      \ 'proof-for-all',
      \ 'proof-eq',
      \ 'proof-contract',
      \ 'proof-requires-validation',
      \ 'proof-result',
      \ 'proof-old',
      \ 'proof-no-overflow',
      \ 'proof-with-invariants',
      \ 'proof-loop-limit',
      \ 'proof-sorted',
      \ 'proof-permutation',
      \ 'proof-allocation',
      \ 'proof-io',
      \ 'proof-global-write',
      \ 'proof-unsafe',
      \ 'proof-external',
      \ 'proof-asm',
      \ 'proof-mutation']
  call s:check('#' . s:proof, 'limProof')
  call s:check(s:proof, '')
  call s:check('#' . s:proof . '-custom', 'limKeyword')
endfor
call s:check('#proof-custom', 'limKeyword')
call s:check('proof', '')
for s:legacy in ['proof-definition', 'proof-theorem', 'proof-inductive']
  call s:check('#' . s:legacy, 'limKeyword')
endfor
for s:declaration in ['theorem', 'math-definition', 'math-inductive']
  call s:check(s:declaration, '')
  call s:check('#' . s:declaration . '-custom', 'limKeyword')
endfor

" Selector heads are metadata; their function/parameter operands are identifiers.
call setline(1, '(#theorem safe (#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user)))')
for [s:token, s:group] in [['#theorem', 'limDeclaration'],
      \ ['#proof-requires-validation', 'limProof'], ['#parameter-of', 'limProof'],
      \ ['safe', ''], ['entry', ''],
      \ ['validate', ''], ['perform', ''], ['user', '']]
  let s:column = stridx(getline(1), s:token) + 1
  for s:byte in range(s:column, s:column + strlen(s:token) - 1)
    call assert_equal(s:group, synIDattr(synID(1, s:byte, 1), 'name'), s:token)
  endfor
endfor
call s:check('#proof-requires-validation-unknown', 'limKeyword')
call s:check('#parameter-of-unknown', 'limKeyword')
call s:check('#pt-sort-unknown', 'limKeyword')
call s:check('#pt-level-imax-unknown', 'limKeyword')

call setline(1, '(#fn example (: value #u64) #u64 (#return (#u64::add-wrap value 1)))')
for [s:token, s:group] in [['#fn', 'limDeclaration'], ['#u64', 'limType'],
      \ ['#return', 'limControl'], ['#u64::add-wrap', 'limOperator']]
  let s:column = stridx(getline(1), s:token) + 1
  call assert_equal(s:group, synIDattr(synID(1, s:column, 1), 'name'))
endfor
call assert_equal('Type', synIDattr(synIDtrans(hlID('limType')), 'name'))
call assert_equal('Operator', synIDattr(synIDtrans(hlID('limOperator')), 'name'))
call assert_equal(synIDattr(synIDtrans(hlID('Keyword')), 'name'),
      \ synIDattr(synIDtrans(hlID('limPin')), 'name'))

if !empty(v:errors)
  for s:error in v:errors
    echomsg s:error
  endfor
  cquit
endif
qa!
