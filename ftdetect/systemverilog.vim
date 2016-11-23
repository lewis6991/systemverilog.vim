if exists("b:did_ftplugin")
    finish
endif

let b:did_ftplugin = 1

autocmd! BufNewFile,BufRead *.sv,*.svh,*.v,*.vh setfiletype systemverilog

