" Detect Lim source files.
augroup lim_filetype
  autocmd!
  autocmd BufRead,BufNewFile *.lim setfiletype lim
augroup END
