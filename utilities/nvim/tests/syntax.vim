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
      \ ['#arg', 'limBuiltinValue'], ['#ref-mut', 'limTypeForm'], ['#slice', 'limTypeForm'],
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
      \ ['// #u64 #return', 'limComment'], ['#\newline', 'limCharacter']]
  " Comments must not swallow the closing delimiters in the nesting fixture.
  if s:group ==# 'limComment'
    call setline(1, s:token)
    call assert_equal(s:group, synIDattr(synID(1, 3, 1), 'name'))
  else
    call s:check(s:token, s:group)
  endif
endfor

" Contract forms use exact tokens; keywords never consume identifier suffixes.
for s:contract in ['requires', 'ensures', 'preserves', 'assume', 'if-valid', 'where', 'old', 'result', 'index-proven']
  call s:check('#' . s:contract, 'limContract')
  call s:check(s:contract, '')
  call s:check('#' . s:contract . '-custom', 'limKeyword')
endfor
call s:check('#theorem', 'limKeyword')
call s:check('#proof-contract', 'limKeyword')
call s:check('#proof-requires-validation-unknown', 'limKeyword')
call s:check('#parameter-of-unknown', 'limKeyword')

call setline(1, '(#fn example (: value #u64) #u64 (#return (#u64::add-wrap value 1)))')
for [s:token, s:group] in [['#fn', 'limDeclaration'], ['#u64', 'limType'],
      \ ['#return', 'limControl'], ['#u64::add-wrap', 'limOperator']]
  let s:column = stridx(getline(1), s:token) + 1
  call assert_equal(s:group, synIDattr(synID(1, s:column, 1), 'name'))
endfor
call setline(1, '#let-mut count : #u64 = 42u64;')
for [s:token, s:group] in [['#let-mut', 'limDeclaration'], [':', 'limSeparator'],
      \ ['#u64', 'limType'], ['=', 'limSeparator'], ['42u64', 'limNumber']]
  let s:column = stridx(getline(1), s:token) + 1
  call assert_equal(s:group, synIDattr(synID(1, s:column, 1), 'name'))
endfor
call assert_equal('Type', synIDattr(synIDtrans(hlID('limType')), 'name'))
call assert_equal('Operator', synIDattr(synIDtrans(hlID('limOperator')), 'name'))
call setline(1, '(#generate #array ((element #u64) (length 4) (name Array4))) (#if-valid (#call #usize::lt ((left index) (right 4usize))) (#call Array4::get ((values values) (index index))) 0u64)')
for [s:token, s:group] in [['#generate', 'limGenerated'], ['#array', 'limTypeForm'],
      \ ['#u64', 'limType'], ['#if-valid', 'limContract'], ['#call', 'limKeyword'],
      \ ['#usize::lt', 'limOperator']]
  let s:column = stridx(getline(1), s:token) + 1
  call assert_equal(s:group, synIDattr(synID(1, s:column, 1), 'name'))
endfor
call assert_equal(synIDattr(synIDtrans(hlID('Keyword')), 'name'),
      \ synIDattr(synIDtrans(hlID('limPin')), 'name'))

for s:section in ['params', 'returns', 'body', 'value']
  call s:check('#' . s:section, 'limSection')
  call s:check('#' . s:section . '-custom', 'limKeyword')
endfor
for s:mode in ['wrap', 'saturate']
  call s:check('#' . s:mode, 'limOperator')
endfor
call setline(1, '(#return : #u64::add-wrap 20 22)')
for [s:token, s:group] in [['#return', 'limControl'], [':', 'limSeparator'], ['#u64::add-wrap', 'limOperator']]
  let s:column = stridx(getline(1), s:token) + 1
  call assert_equal(s:group, synIDattr(synID(1, s:column, 1), 'name'))
endfor
for [s:token, s:group] in [['#body', 'limSection'], ['#requires', 'limContract'],
      \ ['#loop', 'limRepeat'], ['#for-range', 'limRepeat']]
  call setline(1, '{ ' . s:token . ':')
  for s:column in range(3, 2 + strlen(s:token))
    call assert_equal(s:group, synIDattr(synID(1, s:column, 1), 'name'))
  endfor
  call assert_equal('limSeparator', synIDattr(synID(1, 3 + strlen(s:token), 1), 'name'))
  call s:check(s:token . ':custom', 'limKeyword')
  call s:check(s:token . '::custom', 'limKeyword')
endfor
call setline(1, '#fn read { #params={index=#usize;}; #returns=#bool; #body=([#usize; index < 4];); } // comment')
for [s:token, s:group] in [['#fn', 'limDeclaration'], ['#params', 'limSection'],
      \ ['#usize', 'limType'], ['#returns', 'limSection'], ['#bool', 'limType'],
      \ ['#body', 'limSection'], ['<', 'limOperator'], ['=', 'limSeparator'],
      \ [';', 'limSeparator'], ['// comment', 'limComment']]
  let s:column = stridx(getline(1), s:token) + 1
  for s:offset in range(0, strlen(s:token) - 1)
    call assert_equal(s:group, synIDattr(synID(1, s:column + s:offset, 1), 'name'), s:token)
  endfor
endfor

if !empty(v:errors)
  for s:error in v:errors
    echomsg s:error
  endfor
  cquit
endif
qa!
