if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetSystemVerilogIndent()
setlocal indentkeys+=;
setlocal indentkeys+==end
setlocal indentkeys+==else

let s:sv_regions = {
    \ 'svModuleBody'      : { 'start' : '\<module\>'    , 'end' : '\<endmodule\>'             , 'seq' : 1 },
    \ 'svInterfaceBody'   : { 'start' : '\<interface\>' , 'end' : '\<endinterface\>'          , 'seq' : 1 },
    \ 'svProgramBody'     : { 'start' : '\<program\>'   , 'end' : '\<endprogram\>'            , 'seq' : 1 },
    \ 'svClassBody'       : { 'start' : '\<class\>'     , 'end' : '\<endclass\>'              , 'seq' : 0 },
    \ 'svFunctionBody'    : { 'start' : '\<function\>'  , 'end' : '\<endfunction\>'           , 'seq' : 1 },
    \ 'svTaskBody'        : { 'start' : '\<task\>'      , 'end' : '\<endtask\>'               , 'seq' : 1 },
    \ 'svPackageBody'     : { 'start' : '\<package\>'   , 'end' : '\<endpackage\>'            , 'seq' : 1 },
    \ 'svStaticSeqBlock'  : { 'start' : '\<begin\>'     , 'end' : '\<end\>'                   , 'seq' : 1 },
    \ 'svSeqBlock'        : { 'start' : '\<begin\>'     , 'end' : '\<end\>'                   , 'seq' : 1 },
    \ 'svSequenceBody'    : { 'start' : '\<sequence\>'  , 'end' : '\<endsequence\>'           , 'seq' : 0 },
    \ 'svGenerate'        : { 'start' : '\<generate\>'  , 'end' : '\<endgenerate\>'           , 'seq' : 1 },
    \ 'svPropertyBody'    : { 'start' : '\<property\>'  , 'end' : '\<endproperty\>'           , 'seq' : 0 },
    \ 'svCovergroupBody'  : { 'start' : '\<covergroup\>', 'end' : '\<endgroup\>'              , 'seq' : 0 },
    \ 'svAttribute'       : { 'start' : '(\*'           , 'end' : '\*)'                       , 'seq' : 0 },
    \ 'svDo'              : { 'start' : '\<do\>'        , 'end' : '\<while\s*(.*)\s*;'        , 'seq' : 1 },
    \ 'svCase'            : { 'start' : '\<case\>'      , 'end' : '\<endcase\>'               , 'seq' : 1 },
    \ 'svFork'            : { 'start' : '\<fork\>'      , 'end' : '\<join\%(_all\|_none\)\?\>', 'seq' : 1 },
    \ 'svConstraintBody'  : { 'start' : '{'             , 'end' : '}'                         , 'seq' : 1 },
    \ 'svTypeParen'       : { 'start' : '{'             , 'end' : '}'                         , 'seq' : 0 },
    \ 'svConcat'          : { 'start' : '{'             , 'end' : '}'                         , 'seq' : 0 },
    \ 'svCoverpointBins'  : { 'start' : '{'             , 'end' : '}'                         , 'seq' : 0 },
    \ 'svRParen'          : { 'start' : '('             , 'end' : ')'                         , 'seq' : 0 },
    \ 'svArgs'            : { 'start' : '('             , 'end' : ')'                         , 'seq' : 0 },
    \ 'svPropertyParen'   : { 'start' : '('             , 'end' : ')'                         , 'seq' : 0 },
    \ 'svParamDeclList'   : { 'start' : '('             , 'end' : ')'                         , 'seq' : 0 },
    \ 'svPortList'        : { 'start' : '('             , 'end' : ')'                         , 'seq' : 0 },
    \ 'svPortInstanceList': { 'start' : '('             , 'end' : ')'                         , 'seq' : 0 }
    \ }

function! GetSystemVerilogIndent()
    let l:line = getline(v:lnum)
    echom " "

    " Handle some edge-cases first.
    if l:line =~ '^\s*//.*' && getline(v:lnum+1) =~ 'else'
        return indent(v:lnum+1)
    elseif l:line =~ '^\s*else\>'
        return indent(s:GetElseIndent())
    endif

    let l:context = s:SynStack(1)

    let l:sv_region = l:context[0]

    " Prune context for regions that don't determine indentation.
    while l:sv_region != 'TOP'                 &&
        \ !has_key(s:sv_regions, l:sv_region)  &&
        \ l:sv_region != 'svTaskHeader'        &&
        \ l:sv_region != 'svFunctionHeader'    &&
        \ l:sv_region != 'svClassHeader'       &&
        \ l:sv_region != 'svAssign'            &&
        \ l:sv_region != 'svReturn'            &&
        \ l:sv_region != 'svParamAssign'       &&
        \ l:sv_region != 'svImplication'       &&
        \ l:sv_region != 'svComment'           &&
        \ l:sv_region != 'svDefineDeclaration' &&
        \ l:sv_region != 'svImmediateProperty'
        call remove(l:context, 0)
        if len(l:context) > 0
            let l:sv_region = l:context[0]
        else
            let l:sv_region = 'TOP'
            break
        endif
    endwhile

    let l:context_line = 0
    let l:offset = 0

    if l:sv_region == 'svComment'
        let l:context_line = v:lnum-1
    elseif has_key(s:sv_regions, l:sv_region)
        let l:sv_region_details = s:sv_regions[l:sv_region]
        let l:context_line = s:SearchBlockStart(l:sv_region_details['start'], l:sv_region_details['end'])
        if l:line !~ '^\s*'.l:sv_region_details['end']
            if l:sv_region == 'svFork'
                if l:line =~ '^fork\>'
                    return 0
                endif
            endif
            " If the region can contain one-line if statements and such, then we
            " must determine this indent by searching backwards for an anchor
            " point rather than just using the region start.
            if l:sv_region_details['seq']
                let [l:context_line, l:offset] = s:GetSeqBlockIndentAnchor(l:context_line, v:lnum)
            else
                let l:offset += &sw
            endif
            if l:sv_region == 'svCase'
                " Indent if below label
                if getline(prevnonblank(v:lnum-1)) =~ ":\s*$"
                    let l:offset += &sw
                endif
            endif
        endif
    elseif l:sv_region =~ 'sv.*Header'
        if l:sv_region =~ 'svClassHeader'
            let l:context_line = s:SearchBlockStart('\<class\>', '\<endclass\>')
        elseif l:sv_region =~ 'svFunctionHeader'
            let l:context_line = s:SearchBlockStart('\<function\>', '\<endfunction\>')
        elseif l:sv_region =~ 'svTaskHeader'
            let l:context_line = s:SearchBlockStart('\<task\>', '\<endtask\>')
        endif
        let l:offset += &sw
    elseif l:sv_region == 'svAssign'      ||
        \  l:sv_region == 'svParamAssign'
        return s:GetAssignIndent()
    elseif l:sv_region == 'svImplication'
        if l:line =~ '\s*);'
            let l:context_line = s:SearchBlockStart('(', ')')
        else
            return s:GetAssignIndent()
        endif
    elseif l:sv_region == 'svReturn'
        return s:GetReturnIndent()
    elseif l:sv_region == 'svImmediateProperty'
        let l:context_line = s:SearchBlockStart('\<assert\>', ';')
        if l:line !~ '^\s*else\>'
            let l:offset += &sw
        endif
    elseif l:sv_region == 'svDefineDeclaration'
        "Don't change indent as the body of a define has no syntax requirements.
        return indent(v:lnum)
    elseif l:sv_region == 'TOP'
        let [l:context_line, l:offset] = s:GetSeqBlockIndentAnchor(0, v:lnum)
    endif

    if l:context_line == 0
        return 0
    else
        return indent(l:context_line) + l:offset
    endif

endfunction

function! s:GetSeqBlockIndentAnchor(old_context_line, lnum)
    echom "s:GetSeqBlockIndentAnchor: Start ---> " . a:old_context_line . ' ' . a:lnum
    let l:offset = &sw
    let l:context_line = a:old_context_line
    let l:lnum = prevnonblank(a:lnum-1)
    let l:line = s:GetLineStripped(l:lnum)
    echom l:lnum .': [' . l:line . ']'
    while l:line !~ ';\s*$'                 &&
        \ l:line !~ '\<'.'end'    .'\>\s*$' &&
        \ l:line !~ '\<'.'endcase'.'\>\s*$' &&
        \ l:line !~ '\<'.'join\%(_all\|_none\)\?'.'\>\s*$' &&
        \ l:line !~ '`\h\w*(.*)'            &&
        \ l:lnum > a:old_context_line
        if    l:line =~ '^\s*'. 'if'         .'\>' ||
            \ l:line =~ '^\s*'. 'end\s\+if'  .'\>' ||
            \ l:line =~ '^\s*'. 'else'       .'\>' ||
            \ l:line =~ '^\s*'. 'end\s\+else'.'\>' ||
            \ l:line =~ '^\s*'. 'foreach'    .'\>' ||
            \ l:line =~ '^\s*'. 'for'        .'\>' ||
            \ l:line =~ '^\s*'. 'while'      .'\>' ||
            \ l:line =~ '^\s*'. 'always'
            let l:context_line = l:lnum
            echom "s:GetSeqBlockIndentAnchor: Found Indent Anchor: " .  l:context_line . " : [" . l:line . "]"
            if getline(v:lnum) =~ '^\s*begin\>'
                echom "s:GetSeqBlockIndentAnchor: De-indenting due to line starting with 'begin'"
                let l:offset -= &sw
            endif
            break
        endif
        let l:lnum -= 1
        let l:line = getline(prevnonblank(l:lnum))
    endwhile

    echom "s:GetSeqBlockIndentAnchor: End <--- " . l:context_line ." ". l:offset
    return [l:context_line, l:offset]
endfunction

function! s:GetElseIndent()
    echom "s:GetElseIndent: Start --->"
    let l:lnum = v:lnum - 1
    let l:line = getline(prevnonblank(l:lnum))
    if l:line =~ 'end\s*$'
        " Jump over 'begin...end' block
        call cursor(l:lnum, 1)
        let l:context_line = s:SearchBlockStart('begin', 'end')
        echom "s:GetElseIndent: End <--- ".l:context_line
        return l:context_line
    else
        " else must belong to a oneline if or an assert
        while l:line !~ '^\s*\%(\%(else\s\+\)\?if\|assert\)\>'
            let l:lnum -= 1
            let l:line = getline(prevnonblank(l:lnum))
        endwhile
        return l:lnum
    endif
endfunction

function! s:GetAssignIndent()
    echom "s:GetAssignIndent: Start --->"
    let l:lnum = prevnonblank(v:lnum - 1)
    let l:line = getline(l:lnum)

    if l:line =~ '?\s*[^ ]' && getline(v:lnum) !~ '?'
        echom "Ternary"
        return len(substitute(l:line, '?\s*\zs.*', '', ""))
    elseif l:line =~ '[^!>|=]=[^=]\s*[^ ]'
        echom "Assign 1"
        return len(substitute(l:line, '<\?=\s*\zs.*', '', ""))
    elseif l:line =~ '|[-=]>\s*[^ ]'
        echom "Assign 2"
        return len(substitute(l:line, '|[-=]>\s*\zs.*', '', ""))
    elseif l:line =~ '|[-=]>\s*$' ||
        \  l:line =~ '[^!>|=]=\s*$'
        echom "Assign 3"
        return indent(l:lnum) + &sw
    else
        echom "Assign 4"
        return indent(l:lnum)
    endif
endfunction

function! s:GetReturnIndent()
    let l:ret_lnum = search('\<return\>', 'bnW')
    let l:ret_line = getline(l:ret_lnum)
    if l:ret_line =~ "return\s*$"
        return indent(l:ret_lnum)
    else
        return len(substitute(l:ret_line, '\<return\s*\zs.*', '', ""))
    endif
endfunction

function! s:SearchBlockStart(start, end)
    let l:skip_arg =
        \ 'synIDattr(synID(".", col("."), 0), "name") =~ "Comment"'
    return searchpairpos(a:start, '', a:end, 'bnW', l:skip_arg)[0]
endfunction

function! SearchBlockStart(start, end)
    return s:SearchBlockStart(a:start, a:end)
endfunction

function! s:SynStack(col)
    let l:context = reverse(map(synstack(v:lnum, a:col), 'synIDattr(v:val, "name")'))
    if len(l:context) > 0
        return l:context
    else
        return [ 'TOP' ]
    endif
endfunction

function! s:IsComment(lnum)
  return synIDattr(synID(a:lnum, 1, 0), "name") =~ "Comment"
endfunction

function! s:GetLineStripped(lnum)
  if s:IsComment(a:lnum)
    return ""
  endif

  let l:temp = getline(a:lnum)
  " Remove inline comments unless the whole line is a comment
  if l:temp !~ '^\s*//' && l:temp !~ '^\s*/\*.*\*/\s*$'
    let l:temp = substitute(l:temp, '/\*.\{-}\*/\|//.*', '', 'g')
  endif

  " Remove strings
  return substitute(l:temp, '".\{-}"', '""', 'g')
endfunction
